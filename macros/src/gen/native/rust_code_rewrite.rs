//! AST rewriter that lifts panicking Rust arithmetic in user `![...]` blocks
//! into `Option`-returning `SafeArith` calls.
//!
//! # Why this exists
//!
//! Grammar rules can carry arbitrary Rust in `![...]` blocks:
//!
//! ```text
//! AddNum  . a:Num, b:Num |- a "+" b : Num ![a + b]                        step;
//! FactNum . a:Num        |- a "!"   : Num ![{ (1..=a.max(0)).product::<i32>() }] step;
//! ```
//!
//! Rust's `+`, `*`, and `.product::<i32>()` panic on integer overflow in debug
//! mode. Panics inside the evaluator or inside an Ascent rule body cause
//! double-panic SIGABRTs under proptest / nextest because the panic hook runs
//! before `catch_unwind` can intercept. `catch_unwind` is a band-aid; the root
//! cause is producing panics at all.
//!
//! This module provides [`safeify`] which consumes a `syn::Expr` (or `syn::Block`)
//! and returns an expression of type `Option<T>` that:
//!
//! - Replaces every infix arithmetic operator (`+ - * / %`) and unary `-` with
//!   the corresponding [`mettail_runtime::SafeArith`] method, threaded through
//!   `?` so any `None` short-circuits the whole expression.
//! - Replaces `.product::<T>()` / `.sum::<T>()` with
//!   [`SafeArith::safe_product`] / [`SafeArith::safe_sum`].
//! - Replaces `.pow(n)` / `.powi(n)` / `.powf(x)` with `safe_pow` / `safe_powf`.
//! - Replaces `.sqrt()` / `.ln()` / `.log2()` / `.log10()` / `.exp()` /
//!   `.sin()` / `.cos()` / `.tan()` / `.asin()` / `.acos()` / `.atan()` with
//!   [`SafeFloat`] equivalents.
//! - Wraps the whole rewritten body in `(|| -> Option<_> { Some(#rewritten) })()`
//!   so the emission site can use `if let Some(v) = ...` uniformly.
//!
//! # What is *not* rewritten
//!
//! - Method calls on non-arithmetic receivers (`s.len()`, `v.clone()`, …).
//! - Anything inside string literals, `macro!(…)`, or nested closures — the
//!   visitor recurses but only the operator patterns listed above trigger a
//!   rewrite.
//! - `==`, `!=`, `<`, `>`, `&&`, `||`, `!`, `&`, `|`, `^`, `<<`, `>>` — these
//!   do not overflow in a way we need to worry about (shift overflow in debug
//!   mode panics, but shifts are rare in native-eval code; can be added later
//!   if a real case appears).
//!
//! # Float-specific behavior
//!
//! `SafeArith` for `f32`/`f64` / `CanonicalFloat*` returns `None` on `NaN` but
//! preserves `±Inf`. For the rewrite-rule use case we additionally want to
//! reject `Inf` (a rewrite firing that produces `FloatLit(Inf)` creates a
//! stable rule from a nonsense input). The codegen caller — not this rewriter —
//! is responsible for the outer `is_finite` filter. See
//! [`wrap_in_option_closure`].

use proc_macro2::TokenStream;
use quote::quote;
use syn::visit_mut::{self, VisitMut};
use syn::{BinOp, Expr, ExprMethodCall, ExprUnary, UnOp};

/// Rewrite a `syn::Expr` so panicking arithmetic becomes `?`-propagated
/// `SafeArith` calls.
///
/// The returned expression has type `Option<T>` where `T` is the original
/// expression's type. Embed inside `(|| -> Option<_> { Some(#rewritten) })()`
/// or similar via [`wrap_in_option_closure`].
pub fn safeify(expr: &Expr) -> Expr {
    let mut visitor = Safeifier;
    let mut cloned = expr.clone();
    visitor.visit_expr_mut(&mut cloned);
    cloned
}

/// Wrap a rewritten expression in a zero-arg closure that returns
/// `Option<_>`. The result is the form the caller can embed directly into
/// generated code and match on with `if let Some(v) = ...`.
///
/// `rewritten` is expected to be the output of [`safeify`] — an expression
/// that may produce `?` short-circuit failures internally.
///
/// **Lift dispatch:** the inner value passes through
/// `mettail_runtime::lift::Lift(value).lift()` so an expression that already
/// returns `Option<T>` (e.g. `calc_try_int_bin(&a, w)`) is detected by the
/// autoref-specialization on `Lift<Option<T>>` and passes through unchanged
/// — no `Some(Some(…))` double-wrap. A plain-`T` expression (e.g.
/// `safe_add(a, b)?` after rewriting `a + b`) hits the `LiftPlain` trait
/// fallback and gets wrapped as `Some(t)`.
pub fn wrap_in_option_closure(rewritten: &Expr) -> TokenStream {
    quote! {
        (|| -> ::std::option::Option<_> {
            // `LiftPlain` must be in scope to enable trait method dispatch
            // on `&Lift<T>`. The inherent impl on `Lift<Option<T>>` does
            // not require the trait import — it wins regardless.
            #[allow(unused_imports)]
            use ::mettail_runtime::lift::LiftPlain as _;
            #[allow(unused_braces, unused_parens)]
            let __mettail_lifted = ::mettail_runtime::lift::Lift(#rewritten).lift();
            __mettail_lifted
        })()
    }
}

/// Convenience: safeify + wrap in one step. This is the common codegen path.
pub fn safeify_and_wrap(expr: &Expr) -> TokenStream {
    let rewritten = safeify(expr);
    wrap_in_option_closure(&rewritten)
}

/// Method-only safeify: rewrite `.expect(...)` / `.unwrap()` / `.pow()` etc.
/// but leave binary/unary arithmetic operators intact. Use at codegen sites
/// where the user's rust_code pattern-matches inner reference values
/// (`&i32`, `&u32`) and does bare arithmetic on them — `SafeArith` requires
/// owned types, so rewriting `x + y` to `safe_add(x, y)?` would fail to
/// compile with "SafeArith not implemented for &T".
///
/// The returned expression is wrapped in a zero-arg closure that returns
/// `Option<T>`. Methods that could panic short-circuit via `?`; bare
/// operators stay as they were.
pub fn safeify_methods_and_wrap(expr: &Expr) -> TokenStream {
    let mut cloned = expr.clone();
    let mut visitor = MethodOnlySafeifier;
    visitor.visit_expr_mut(&mut cloned);
    wrap_in_option_closure(&cloned)
}

// ─── The visitor ────────────────────────────────────────────────────────────

struct Safeifier;

/// Visitor that only rewrites method calls (`.expect`, `.unwrap`, `.pow`…),
/// leaving binary operators alone. See `safeify_methods_and_wrap`.
struct MethodOnlySafeifier;

impl VisitMut for MethodOnlySafeifier {
    fn visit_expr_mut(&mut self, node: &mut Expr) {
        visit_mut::visit_expr_mut(self, node);
        if let Expr::MethodCall(mc) = node {
            if let Some(replacement) = rewrite_method_call(mc) {
                *node = replacement;
            }
        }
    }
}

impl VisitMut for Safeifier {
    fn visit_expr_mut(&mut self, node: &mut Expr) {
        // Recurse first so inner operators are rewritten before we look at the
        // current node — `(a + b) * c` must rewrite `a + b` to
        // `SafeArith::safe_add(a, b)?` before we can wrap the outer `*`.
        visit_mut::visit_expr_mut(self, node);

        // Then pattern-match on the (now potentially-rewritten) node.
        match node {
            Expr::Binary(eb) => {
                if let Some(method) = binop_to_safe_method(&eb.op) {
                    let lhs = &eb.left;
                    let rhs = &eb.right;
                    // Use fully-qualified `SafeArith` path so the generated code
                    // does not require the user to `use mettail_runtime::SafeArith`.
                    *node = syn::parse_quote! {
                        <_ as ::mettail_runtime::SafeArith>::#method(#lhs, #rhs)?
                    };
                }
            },
            Expr::Unary(ExprUnary { op: UnOp::Neg(_), expr: inner, .. }) => {
                let e = inner;
                *node = syn::parse_quote! {
                    <_ as ::mettail_runtime::SafeArith>::safe_neg(#e)?
                };
            },
            Expr::Unary(ExprUnary { op: UnOp::Not(_), expr: inner, .. }) => {
                let e = inner;
                *node = syn::parse_quote! {
                    <_ as ::mettail_runtime::SafeArith>::safe_not(#e)?
                };
            },
            Expr::MethodCall(mc) => {
                if let Some(replacement) = rewrite_method_call(mc) {
                    *node = replacement;
                }
            },
            _ => {},
        }
    }
}

/// Map a binary operator to its `SafeArith` method name. Returns `None` if we
/// don't rewrite this operator.
fn binop_to_safe_method(op: &BinOp) -> Option<syn::Ident> {
    use proc_macro2::Span;
    let name = match op {
        BinOp::Add(_) => "safe_add",
        BinOp::Sub(_) => "safe_sub",
        BinOp::Mul(_) => "safe_mul",
        BinOp::Div(_) => "safe_div",
        BinOp::Rem(_) => "safe_rem",
        _ => return None,
    };
    Some(syn::Ident::new(name, Span::call_site()))
}

/// If a `.method(...)` call is one of our rewrite targets, return the
/// replacement `Expr`. Otherwise return `None` (visitor leaves it alone).
fn rewrite_method_call(mc: &ExprMethodCall) -> Option<Expr> {
    let recv = &mc.receiver;
    let args = &mc.args;
    let method_name = mc.method.to_string();

    // `.expect(msg)` — user wrote "panic on None/Err with message" but inside
    // a `safeify_and_wrap` closure we want short-circuit instead of panic.
    // Rewrite to `?` so the wrapper returns None. The panic message is
    // discarded (fold rules don't carry Result errors). This also applies
    // to `.unwrap_or_else(|_| panic!(...))` via chained rewrites — but the
    // common case in user grammar code is `.expect(...)`.
    if args.len() == 1 && method_name == "expect" {
        return Some(syn::parse_quote! {
            (#recv)?
        });
    }

    // `.unwrap()` — same rewrite. Panicking on None/Err becomes short-circuit.
    if args.is_empty() && method_name == "unwrap" {
        return Some(syn::parse_quote! {
            (#recv)?
        });
    }

    // Phase D Layer 1 (2026-05-17): `.eval()` (zero-arg) — user-grammar
    // code in fold rules often calls `.eval()` on AST node references
    // (e.g., `Proc::ProcBigInt(n) => n.as_ref().eval()` in
    // `Bool::ProcToBool`). The `eval()` method panics on Var-bearing /
    // unreduced terms; `try_eval()` returns `Option`. Under Phase D's
    // all-alts seeding, fold-rule LHSs can match against alts whose
    // sub-terms haven't been reduced yet, so calling `eval()` would
    // panic — the regressing pattern in 46 edge_case tests.
    //
    // Rewriting `<recv>.eval()` → `(<recv>).try_eval()?` makes user
    // grammar code Var-safe by construction. The enclosing
    // `safeify_and_wrap` closure returns `Option<_>`, so `?` short-
    // circuits to None on Var-bearing terms — evidence-driven rule-out
    // per the preserve-all-derivations mandate (P3: try_eval=None IS
    // evidence the term didn't reduce). The arm whose `.eval()` short-
    // circuits simply doesn't contribute its term to the result; other
    // alts whose sub-terms ARE reduced contribute normally.
    if args.is_empty() && method_name == "eval" {
        return Some(syn::parse_quote! {
            (#recv).try_eval()?
        });
    }

    // Single-arg arithmetic methods.
    if args.len() == 1 {
        match method_name.as_str() {
            // `.pow(n)` / `.powi(n)` — integer exponent. Map to `safe_pow` (which
            // takes i32 in both the integer and float impls).
            "pow" | "powi" => {
                let exp = args.iter().next().unwrap();
                return Some(syn::parse_quote! {
                    <_ as ::mettail_runtime::SafeArith>::safe_pow(#recv, (#exp) as i32)?
                });
            },
            // `.powf(x)` — float exponent. SafeFloat-only.
            "powf" => {
                let exp = args.iter().next().unwrap();
                return Some(syn::parse_quote! {
                    <_ as ::mettail_runtime::SafeFloat>::safe_powf(#recv, #exp)?
                });
            },
            _ => {},
        }
    }

    // Zero-arg unary methods (SafeFloat transcendentals).
    if args.is_empty() {
        let safe_method = match method_name.as_str() {
            "sqrt" => Some("safe_sqrt"),
            "ln" => Some("safe_ln"),
            "log2" => Some("safe_log2"),
            "log10" => Some("safe_log10"),
            "exp" => Some("safe_exp"),
            "sin" => Some("safe_sin"),
            "cos" => Some("safe_cos"),
            "tan" => Some("safe_tan"),
            "asin" => Some("safe_asin"),
            "acos" => Some("safe_acos"),
            "atan" => Some("safe_atan"),
            _ => None,
        };
        if let Some(name) = safe_method {
            let ident = syn::Ident::new(name, proc_macro2::Span::call_site());
            return Some(syn::parse_quote! {
                <_ as ::mettail_runtime::SafeFloat>::#ident(#recv)?
            });
        }

        // `.product::<T>()` / `.sum::<T>()` — iterator folds.
        if method_name == "product" || method_name == "sum" {
            let safe = if method_name == "product" {
                "safe_product"
            } else {
                "safe_sum"
            };
            let ident = syn::Ident::new(safe, proc_macro2::Span::call_site());
            // The turbofish (`::<T>`) is in `mc.turbofish`. If present, we forward it
            // so the caller gets the same explicit element type they asked for.
            if let Some(ref turbofish) = mc.turbofish {
                // turbofish is `::<T, ...>`; we want the first type argument T.
                // `safe_product` is generic over Self via the trait impl, so the
                // element type must be threaded as the trait receiver. Easiest
                // way: call `<T as SafeArith>::safe_product(iter)`.
                if let Some(first_ty) = turbofish.args.first() {
                    return Some(syn::parse_quote! {
                        <#first_ty as ::mettail_runtime::SafeArith>::#ident(#recv)?
                    });
                }
            }
            // No turbofish — type inferred from context. Use the default path.
            return Some(syn::parse_quote! {
                <_ as ::mettail_runtime::SafeArith>::#ident(#recv)?
            });
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens;

    fn normalise(tokens: TokenStream) -> String {
        // Reduce whitespace noise so comparisons are robust against syn's formatting.
        let s = tokens.to_string();
        s.split_whitespace().collect::<Vec<_>>().join(" ")
    }

    fn safeify_str(src: &str) -> String {
        let expr: Expr = syn::parse_str(src).expect("parse");
        let rewritten = safeify(&expr);
        normalise(rewritten.to_token_stream())
    }

    #[test]
    fn rewrites_add() {
        let out = safeify_str("a + b");
        assert!(out.contains("safe_add"), "expected safe_add in {}", out);
        assert!(out.contains("?"), "expected ? propagation in {}", out);
    }

    #[test]
    fn rewrites_sub_mul_div_rem() {
        for (src, method) in [
            ("a - b", "safe_sub"),
            ("a * b", "safe_mul"),
            ("a / b", "safe_div"),
            ("a % b", "safe_rem"),
        ] {
            let out = safeify_str(src);
            assert!(out.contains(method), "expected {} in rewrite of {}: {}", method, src, out);
        }
    }

    #[test]
    fn rewrites_unary_neg() {
        let out = safeify_str("-a");
        assert!(out.contains("safe_neg"), "expected safe_neg in {}", out);
    }

    #[test]
    fn rewrites_nested() {
        // (a + b) * c should become
        //   SafeArith::safe_mul(SafeArith::safe_add(a, b)?, c)?
        let out = safeify_str("(a + b) * c");
        assert!(out.contains("safe_add"), "expected safe_add in {}", out);
        assert!(out.contains("safe_mul"), "expected safe_mul in {}", out);
    }

    #[test]
    fn rewrites_pow() {
        let out = safeify_str("a.pow(n)");
        assert!(out.contains("safe_pow"), "expected safe_pow in {}", out);
    }

    #[test]
    fn rewrites_powf() {
        let out = safeify_str("a.powf(0.5)");
        assert!(out.contains("safe_powf"), "expected safe_powf in {}", out);
    }

    #[test]
    fn rewrites_sqrt_ln_exp() {
        for (src, method) in [
            ("a.sqrt()", "safe_sqrt"),
            ("a.ln()", "safe_ln"),
            ("a.exp()", "safe_exp"),
            ("a.log2()", "safe_log2"),
            ("a.log10()", "safe_log10"),
            ("a.sin()", "safe_sin"),
            ("a.cos()", "safe_cos"),
            ("a.tan()", "safe_tan"),
            ("a.asin()", "safe_asin"),
            ("a.acos()", "safe_acos"),
            ("a.atan()", "safe_atan"),
        ] {
            let out = safeify_str(src);
            assert!(out.contains(method), "expected {} in rewrite of {}: {}", method, src, out);
        }
    }

    #[test]
    fn rewrites_product_with_turbofish() {
        let out = safeify_str("(1..=a.max(0)).product::<i32>()");
        assert!(out.contains("safe_product"), "expected safe_product in {}", out);
        assert!(out.contains("i32"), "expected i32 type annotation in {}", out);
    }

    #[test]
    fn rewrites_sum_with_turbofish() {
        let out = safeify_str("xs.iter().sum::<i64>()");
        assert!(out.contains("safe_sum"), "expected safe_sum in {}", out);
    }

    #[test]
    fn leaves_comparison_operators_alone() {
        let out = safeify_str("a == b");
        assert!(!out.contains("safe_"), "== should not be rewritten: {}", out);
        let out = safeify_str("a && b");
        assert!(!out.contains("safe_"), "&& should not be rewritten: {}", out);
    }

    #[test]
    fn leaves_non_arith_methods_alone() {
        let out = safeify_str("s.len()");
        assert!(!out.contains("safe_"), "s.len() should be untouched: {}", out);
        let out = safeify_str("v.clone()");
        assert!(!out.contains("safe_"), "v.clone() should be untouched: {}", out);
    }

    #[test]
    fn wraps_in_option_closure() {
        let expr: Expr = syn::parse_str("a + b").expect("parse");
        let wrapped = safeify_and_wrap(&expr);
        let s = normalise(wrapped);
        assert!(s.contains("Option"), "expected Option wrapper: {}", s);
        // The wrapper uses `Lift(...).lift()` (LiftPlain trait) rather than a
        // literal `Some(...)` — it works for both Option<T> and plain T.
        assert!(s.contains("Lift"), "expected Lift wrapper: {}", s);
        assert!(s.contains(". lift ()"), "expected .lift() call: {}", s);
        assert!(s.contains("safe_add"), "expected safe_add in body: {}", s);
    }

    #[test]
    fn factorial_block_rewrites() {
        // Main use case: FactNum's `{ (1..=a.max(0)).product::<i32>() }`
        let out = safeify_str("{ (1..=a.max(0)).product::<i32>() }");
        assert!(out.contains("safe_product"), "expected safe_product: {}", out);
        assert!(out.contains("i32"), "expected i32 annotation: {}", out);
    }

    #[test]
    fn addition_inside_method_args_rewrites() {
        // `foo(a + b)` — the `a + b` inside the call should be rewritten.
        let out = safeify_str("foo(a + b)");
        assert!(out.contains("safe_add"), "expected nested safe_add: {}", out);
    }
}
