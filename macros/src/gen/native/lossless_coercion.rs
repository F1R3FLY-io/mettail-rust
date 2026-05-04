//! Stage 3.12.9 β-1 (2026-05-04): emit lossless coercion expressions
//! for Stage 3.13 auto-injection wrappers in `try_eval`.
//!
//! ## Why
//!
//! Stage 3.13 auto-injection emits synthetic `<Source>To<Target>`
//! constructors for every lossless edge in `NativeKind::lossless_targets()`
//! (e.g., `BigRat::FloatToBigRat(Box<Float>)`). Pre-Stage-3.12.9, these
//! synthetic variants fell through `try_eval`'s catch-all `_ => None` —
//! parsing `str(2.0)` lands `Proc::ToStr(Proc::CastBigRat(BigRat::FloatToBigRat(
//! Float::FloatLit(2.0))))` and the user's `ToStr` rule body calls
//! `.eval()` (panicking) on the wrapper.
//!
//! Stage 3.12.9 β closes this algebraic gap by extending `try_eval`
//! codegen: when a rule satisfies `is_auto_injected == true` AND
//! `classify_simple_projection_shape(rule).is_some()` AND the (source,
//! target) lossless edge is in `NativeKind::lossless_targets`, emit a
//! `try_eval` arm that recursively evaluates the inner term via
//! `inner.try_eval()?` and applies the coercion via the helper here.
//!
//! ## Cross-cat recursion
//!
//! Same idiom as calc's existing PDA `BigRat::Fraction(a, b)` arm at
//! `target/generated/calculator/eval.rs:1002-1009` — direct
//! `inner.try_eval()?` cross-cat call. Bounded by lossless-lattice depth
//! (≤ 4 hops in practice: e.g., `Int → BigInt → BigRat`).
//!
//! ## Source / target storage types
//!
//! These match what `try_eval` returns for each kind, per
//! `eval.rs:838-844`:
//!
//!   * `Bool`              → `bool`
//!   * `IntN`              → `iN` (i8/i16/i32/i64/i128/isize)
//!   * `UIntN`             → `uN` (u8/u16/u32/u64/u128/usize)
//!   * `Float32`           → `mettail_runtime::CanonicalFloat32`
//!   * `Float64`           → `mettail_runtime::CanonicalFloat64`
//!   * `CanonicalBigInt`   → `mettail_runtime::CanonicalBigInt`
//!   * `CanonicalBigRat`   → `mettail_runtime::CanonicalBigRat`
//!   * `CanonicalFixedPoint` → `mettail_runtime::CanonicalFixedPoint`
//!
//! The emitted expression evaluates to target's storage type. Fallible
//! coercions (Float→BigRat for non-finite inputs) embed `.ok()?` and so
//! must be evaluated inside an `Option`-returning function — which
//! `try_eval` is.

use mettail_ast::language::NativeKind;
use proc_macro2::TokenStream;
use quote::quote;

/// Build the coercion expression for a lossless edge `source → target`.
///
/// `inner_expr` is a token stream for an expression of source's storage
/// type (typically a binding name like `__v`). The returned expression
/// evaluates to target's storage type.
///
/// Returns `None` when the edge is not in the lossless lattice (caller
/// falls through to `_ => None` in `try_eval`).
pub fn build_lossless_coercion(
    source: NativeKind,
    target: NativeKind,
    inner_expr: &TokenStream,
) -> Option<TokenStream> {
    // Sanity gate: only emit when the lattice declares the edge as
    // lossless. Same source-of-truth as auto_inject.rs uses for
    // emitting the synthetic constructor.
    if !source.lossless_targets().contains(&target) {
        return None;
    }

    use NativeKind::*;
    Some(match (source, target) {
        // ─── Bool source ─────────────────────────────────────────────
        (Bool, Int8) => quote! { (#inner_expr) as i8 },
        (Bool, Int16) => quote! { (#inner_expr) as i16 },
        (Bool, Int32) => quote! { (#inner_expr) as i32 },
        (Bool, Int64) => quote! { (#inner_expr) as i64 },
        (Bool, Int128) => quote! { (#inner_expr) as i128 },
        (Bool, Isize) => quote! { (#inner_expr) as isize },
        (Bool, UInt8) => quote! { (#inner_expr) as u8 },
        (Bool, UInt16) => quote! { (#inner_expr) as u16 },
        (Bool, UInt32) => quote! { (#inner_expr) as u32 },
        (Bool, UInt64) => quote! { (#inner_expr) as u64 },
        (Bool, UInt128) => quote! { (#inner_expr) as u128 },
        (Bool, Usize) => quote! { (#inner_expr) as usize },
        (Bool, CanonicalBigInt) => quote! {
            ::mettail_runtime::CanonicalBigInt::from(::num_bigint::BigInt::from(if #inner_expr { 1i64 } else { 0i64 }))
        },
        (Bool, CanonicalBigRat) => quote! {
            ::mettail_runtime::cast_bigrat_from_i64(if #inner_expr { 1i64 } else { 0i64 })
        },

        // ─── Signed integer source (IntN) ────────────────────────────
        // IntN → IntM widening (N ≤ M).
        (Int8 | Int16 | Int32 | Int64 | Int128 | Isize, t) if t.is_native_signed_int() => {
            let target_ty = t.signed_int_token().expect("signed-int target");
            quote! { (#inner_expr) as #target_ty }
        }
        // IntN → CanonicalBigInt.
        (Int8 | Int16 | Int32 | Int64 | Int128 | Isize, CanonicalBigInt) => quote! {
            ::mettail_runtime::CanonicalBigInt::from(::num_bigint::BigInt::from(#inner_expr))
        },
        // IntN → CanonicalBigRat.
        (Int8 | Int16 | Int32 | Int64 | Int128 | Isize, CanonicalBigRat) => quote! {
            ::mettail_runtime::cast_bigrat_from_bigint(&::num_bigint::BigInt::from(#inner_expr))
        },

        // ─── Unsigned integer source (UIntN) ─────────────────────────
        // UIntN → UIntM widening (N ≤ M).
        (UInt8 | UInt16 | UInt32 | UInt64 | UInt128 | Usize, t) if t.is_native_unsigned_int() => {
            let target_ty = t.unsigned_int_token().expect("unsigned-int target");
            quote! { (#inner_expr) as #target_ty }
        }
        // UIntN → IntM (N < M, sign bit available).
        (UInt8 | UInt16 | UInt32 | UInt64 | UInt128 | Usize, t) if t.is_native_signed_int() => {
            let target_ty = t.signed_int_token().expect("signed-int target");
            quote! { (#inner_expr) as #target_ty }
        }
        // UIntN → CanonicalBigInt.
        (UInt8 | UInt16 | UInt32 | UInt64 | UInt128 | Usize, CanonicalBigInt) => quote! {
            ::mettail_runtime::CanonicalBigInt::from(::num_bigint::BigInt::from(#inner_expr))
        },
        // UIntN → CanonicalBigRat.
        (UInt8 | UInt16 | UInt32 | UInt64 | UInt128 | Usize, CanonicalBigRat) => quote! {
            ::mettail_runtime::cast_bigrat_from_bigint(&::num_bigint::BigInt::from(#inner_expr))
        },

        // ─── Float32 source ──────────────────────────────────────────
        (Float32, Float64) => quote! {
            ::mettail_runtime::CanonicalFloat64::from(f64::from((#inner_expr).get()))
        },
        (Float32, CanonicalBigRat) => quote! {
            ::mettail_runtime::cast_bigrat_from_f64(f64::from((#inner_expr).get())).ok()?
        },

        // ─── Float64 source ──────────────────────────────────────────
        (Float64, CanonicalBigRat) => quote! {
            ::mettail_runtime::cast_bigrat_from_f64((#inner_expr).get()).ok()?
        },

        // ─── CanonicalBigInt source ──────────────────────────────────
        (CanonicalBigInt, CanonicalBigRat) => quote! {
            ::mettail_runtime::cast_bigrat_from_bigint((#inner_expr).get())
        },

        // ─── CanonicalFixedPoint source ──────────────────────────────
        (CanonicalFixedPoint, CanonicalBigRat) => quote! {
            ::mettail_runtime::cast_bigrat_from_fixed(&(#inner_expr))
        },

        // Anything else: lattice contained the edge but we have no
        // emitter — treat as None (caller falls through to `_ => None`).
        // This branch is conservative: as new lossless edges are added
        // to `lossless_targets()`, the emitter must be extended in
        // lockstep. Returning None here keeps codegen sound (no panic,
        // no mis-coerced values) while flagging the gap via the
        // surface bug class (test failures on the relevant wrapper).
        _ => return None,
    })
}

/// Helpers used by the match arms above. Localized to this module so
/// downstream code keeps using `NativeKind`'s public API only.
trait NativeKindExt {
    fn is_native_signed_int(self) -> bool;
    fn is_native_unsigned_int(self) -> bool;
    fn signed_int_token(self) -> Option<TokenStream>;
    fn unsigned_int_token(self) -> Option<TokenStream>;
}

impl NativeKindExt for NativeKind {
    fn is_native_signed_int(self) -> bool {
        matches!(
            self,
            NativeKind::Int8
                | NativeKind::Int16
                | NativeKind::Int32
                | NativeKind::Int64
                | NativeKind::Int128
                | NativeKind::Isize
        )
    }

    fn is_native_unsigned_int(self) -> bool {
        matches!(
            self,
            NativeKind::UInt8
                | NativeKind::UInt16
                | NativeKind::UInt32
                | NativeKind::UInt64
                | NativeKind::UInt128
                | NativeKind::Usize
        )
    }

    fn signed_int_token(self) -> Option<TokenStream> {
        Some(match self {
            NativeKind::Int8 => quote! { i8 },
            NativeKind::Int16 => quote! { i16 },
            NativeKind::Int32 => quote! { i32 },
            NativeKind::Int64 => quote! { i64 },
            NativeKind::Int128 => quote! { i128 },
            NativeKind::Isize => quote! { isize },
            _ => return None,
        })
    }

    fn unsigned_int_token(self) -> Option<TokenStream> {
        Some(match self {
            NativeKind::UInt8 => quote! { u8 },
            NativeKind::UInt16 => quote! { u16 },
            NativeKind::UInt32 => quote! { u32 },
            NativeKind::UInt64 => quote! { u64 },
            NativeKind::UInt128 => quote! { u128 },
            NativeKind::Usize => quote! { usize },
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::Span;
    use syn::Ident;

    fn v_expr() -> TokenStream {
        let v = Ident::new("__v", Span::call_site());
        quote! { #v }
    }

    fn render(ts: TokenStream) -> String {
        ts.to_string()
    }

    #[test]
    fn float64_to_bigrat_uses_cast_bigrat_from_f64_with_ok_question() {
        let coerced = build_lossless_coercion(
            NativeKind::Float64,
            NativeKind::CanonicalBigRat,
            &v_expr(),
        )
        .expect("Float64 → BigRat is lossless");
        let s = render(coerced);
        assert!(s.contains("cast_bigrat_from_f64"), "got: {}", s);
        assert!(s.contains(". ok () ?") || s.contains(".ok()?"), "got: {}", s);
    }

    #[test]
    fn float32_to_bigrat_widens_via_f64_first() {
        let coerced = build_lossless_coercion(
            NativeKind::Float32,
            NativeKind::CanonicalBigRat,
            &v_expr(),
        )
        .expect("Float32 → BigRat is lossless");
        let s = render(coerced);
        assert!(s.contains("f64 :: from") || s.contains("f64::from"), "got: {}", s);
        assert!(s.contains("cast_bigrat_from_f64"), "got: {}", s);
    }

    #[test]
    fn int_to_bigrat_via_bigint_intermediate() {
        let coerced = build_lossless_coercion(
            NativeKind::Int32,
            NativeKind::CanonicalBigRat,
            &v_expr(),
        )
        .expect("Int32 → BigRat is lossless");
        let s = render(coerced);
        assert!(s.contains("cast_bigrat_from_bigint"), "got: {}", s);
        assert!(s.contains("BigInt :: from") || s.contains("BigInt::from"), "got: {}", s);
    }

    #[test]
    fn bigint_to_bigrat_uses_get() {
        let coerced = build_lossless_coercion(
            NativeKind::CanonicalBigInt,
            NativeKind::CanonicalBigRat,
            &v_expr(),
        )
        .expect("BigInt → BigRat is lossless");
        let s = render(coerced);
        assert!(s.contains("cast_bigrat_from_bigint"), "got: {}", s);
        assert!(s.contains(". get ()") || s.contains(".get()"), "got: {}", s);
    }

    #[test]
    fn fixed_to_bigrat_uses_cast_bigrat_from_fixed() {
        let coerced = build_lossless_coercion(
            NativeKind::CanonicalFixedPoint,
            NativeKind::CanonicalBigRat,
            &v_expr(),
        )
        .expect("Fixed → BigRat is lossless");
        let s = render(coerced);
        assert!(s.contains("cast_bigrat_from_fixed"), "got: {}", s);
    }

    #[test]
    fn bool_to_bigrat_uses_cast_bigrat_from_i64() {
        let coerced = build_lossless_coercion(
            NativeKind::Bool,
            NativeKind::CanonicalBigRat,
            &v_expr(),
        )
        .expect("Bool → BigRat is lossless");
        let s = render(coerced);
        assert!(s.contains("cast_bigrat_from_i64"), "got: {}", s);
    }

    #[test]
    fn bool_to_int32_uses_as_cast() {
        let coerced = build_lossless_coercion(
            NativeKind::Bool,
            NativeKind::Int32,
            &v_expr(),
        )
        .expect("Bool → Int32 is lossless");
        let s = render(coerced);
        assert!(s.contains("as i32"), "got: {}", s);
    }

    #[test]
    fn int8_widens_to_int32_via_as_cast() {
        let coerced = build_lossless_coercion(
            NativeKind::Int8,
            NativeKind::Int32,
            &v_expr(),
        )
        .expect("Int8 → Int32 is lossless");
        let s = render(coerced);
        assert!(s.contains("as i32"), "got: {}", s);
    }

    #[test]
    fn uint8_widens_to_int16_via_as_cast() {
        let coerced = build_lossless_coercion(
            NativeKind::UInt8,
            NativeKind::Int16,
            &v_expr(),
        )
        .expect("UInt8 → Int16 is lossless");
        let s = render(coerced);
        assert!(s.contains("as i16"), "got: {}", s);
    }

    #[test]
    fn lossy_edge_returns_none() {
        // Float → IntN is lossy (truncation): not in lossless_targets.
        assert!(
            build_lossless_coercion(
                NativeKind::Float64,
                NativeKind::Int32,
                &v_expr(),
            )
            .is_none(),
            "Float64 → Int32 is lossy; helper must return None"
        );
    }

    #[test]
    fn unsupported_edge_returns_none() {
        // Str source has no lossless targets at all.
        assert!(
            build_lossless_coercion(NativeKind::Str, NativeKind::Bool, &v_expr())
                .is_none(),
            "Str source has no lossless targets; helper must return None"
        );
    }

    #[test]
    fn other_kind_returns_none() {
        // `Other` represents a non-built-in user wrapper — never a
        // lossless source.
        assert!(
            build_lossless_coercion(
                NativeKind::Other,
                NativeKind::CanonicalBigRat,
                &v_expr(),
            )
            .is_none(),
            "Other source has no lossless targets; helper must return None"
        );
    }
}
