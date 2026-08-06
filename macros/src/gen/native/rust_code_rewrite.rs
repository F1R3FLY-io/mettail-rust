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
//! and returns an expression of type `Result<T, Partiality>` that:
//!
//! - Replaces every infix arithmetic operator (`+ - * / %`) and unary `-` with
//!   the corresponding [`mettail_runtime::SafeArith`] method, threaded through
//!   `?` so a decline short-circuits the whole expression **carrying its reason**.
//! - Replaces `.product::<T>()` / `.sum::<T>()` with
//!   [`SafeArith::safe_product`] / [`SafeArith::safe_sum`].
//! - Replaces `.pow(n)` / `.powi(n)` / `.powf(x)` with `safe_pow` / `safe_powf`.
//! - Replaces `.sqrt()` / `.ln()` / `.log2()` / `.log10()` / `.exp()` /
//!   `.sin()` / `.cos()` / `.tan()` / `.asin()` / `.acos()` / `.atan()` with
//!   [`SafeFloat`] equivalents.
//! - Wraps the whole rewritten body in
//!   `(|| -> Result<_, Partiality> { Ok(#rewritten) })()` so the emission site
//!   can decide uniformly what to do with the reason.
//!
//! # ★★ The rewrite is from a panic to a REPORTED disposition, not to an absence
//!
//! Until 2026-07-29 this pass rewrote `.expect(msg)` and `.unwrap()` to a bare
//! `(recv)?`, and its own comment said outright *"The panic message is
//! discarded."* Three Calculator fold bodies were written
//! `.expect("ElemList: invalid index")`, `.expect("DeleteList: invalid index")`
//! and `.expect("get: key not found")` — three deliberate, message-carrying
//! failures — and all three became an unlabelled short-circuit. **The authors'
//! intent was to err; the machinery silently converted it to defer and threw
//! away three good messages.**
//!
//! The rewrite now targets [`mettail_runtime::Partiality`], so each demotion
//! keeps what it knows:
//!
//! | written | emitted | reported as |
//! |---|---|---|
//! | `a + b` | `SafeArith::safe_add(a, b)?` | `Undefined{…}` / `NotRepresentable{…}` — the carrier and reason |
//! | `x.expect(LIT)` | `Declarable::declared(x, LIT)?` | `Declared{message: LIT}` — **the author's own words** |
//! | `x.unwrap()` | `Declarable::unwrapped(x)?` | `Unreported` — declined, and no reason was declared |
//! | `t.eval()` | `not_reduced(t.try_eval())?` | `NotReduced` — **structural**, defers, records nothing |
//!
//! ⚠ `.expect(…)` with a NON-literal argument is refused at expansion time
//! rather than silently degraded: the whole subject of this pass is that a
//! declared message must not be dropped. See [`rewrite_method_call`].
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
/// The returned expression has type `Result<T, Partiality>` where `T` is the
/// original expression's type. Embed inside
/// `(|| -> Result<_, Partiality> { Ok(#rewritten) })()` or similar via
/// [`wrap_in_result_closure`].
pub fn safeify(expr: &Expr) -> Expr {
    let mut visitor = Safeifier;
    let mut cloned = expr.clone();
    visitor.visit_expr_mut(&mut cloned);
    cloned
}

/// Wrap a rewritten expression in a zero-arg closure that returns
/// `Result<_, Partiality>`. The result is the form the caller can embed
/// directly into generated code and classify with
/// `mettail_runtime::partiality::classify`.
///
/// `rewritten` is expected to be the output of [`safeify`] — an expression
/// that may produce `?` short-circuit declines internally, each carrying the
/// reason it declined.
///
/// **Lift dispatch:** the inner value passes through
/// `mettail_runtime::lift::Lift(value).lift()` so an expression that already
/// reports its own partiality (`Result<T, Partiality>`) or that returns a bare
/// `Option<T>` (e.g. `calc_try_int_bin(&a, w)`) is detected by the
/// autoref-specialization inherent impls and converted exactly once — no
/// `Ok(Ok(…))` / `Ok(Some(…))` double-wrap. A plain-`T` expression (e.g.
/// `safe_add(a, b)?` after rewriting `a + b`) hits the `LiftPlain` trait
/// fallback and gets wrapped as `Ok(t)`.
pub fn wrap_in_result_closure(rewritten: &Expr) -> TokenStream {
    quote! {
        (|| -> ::core::result::Result<_, ::mettail_runtime::Partiality> {
            // `LiftPlain` must be in scope to enable trait method dispatch
            // on `&Lift<T>`. The inherent impls on `Lift<Option<T>>` /
            // `Lift<Result<T, Partiality>>` do not require the trait import —
            // they win regardless.
            #[allow(unused_imports)]
            use ::mettail_runtime::lift::LiftPlain as _;
            #[allow(unused_braces, unused_parens)]
            let __mettail_lifted = ::mettail_runtime::lift::Lift(#rewritten).lift();
            __mettail_lifted
        })()
    }
}

/// safeify + wrap, yielding an `Option<_>` — the shape the *evaluator* lanes
/// (`try_eval`, the PDA visit arms, the Rho ground-eval and native-handler fns)
/// consume, all of which return `Option` themselves and have no run report to
/// write a reason into.
///
/// ⚠ The reason is COMPUTED here and dropped by `.ok()` at this boundary. That
/// is a property of the *consumer*, not of the rewrite: the same body emitted
/// through [`safeify_and_wrap_reported`] on the Dovetail fold lane keeps its
/// reason all the way into the run report. Nothing is discarded before the
/// boundary, so widening one of these lanes later is a local change.
pub fn safeify_and_wrap(expr: &Expr) -> TokenStream {
    let reported = safeify_and_wrap_reported(expr);
    quote! { ::core::result::Result::ok(#reported) }
}

/// safeify + wrap, yielding `Result<_, Partiality>` — the shape the Dovetail
/// fold dispatcher consumes so a decline can be REPORTED rather than merely
/// deferred. This is the reporting path; [`safeify_and_wrap`] is the same
/// rewrite with the reason dropped at the consumer's boundary.
pub fn safeify_and_wrap_reported(expr: &Expr) -> TokenStream {
    let rewritten = safeify(expr);
    wrap_in_result_closure(&rewritten)
}

// ─── The visitor ────────────────────────────────────────────────────────────

struct Safeifier;

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

    // ★★ `.expect(msg)` — the author wrote "fail HERE, and here is why". Inside a safeify
    // closure we must not panic (a panic runs with the e-graph mid-saturation and is not
    // containable under cg_clif), so the call is demoted to a `?` short-circuit — but the
    // demotion CARRIES the author's message into `Partiality::Declared` instead of dropping it.
    //
    // ⚠ Until 2026-07-29 this arm emitted a bare `(#recv)?` and its comment read "The panic
    // message is discarded." Three Calculator fold bodies lost their messages that way. The
    // partition rule says a declared failure IS an error the deployer must act on, so the words
    // the author chose are exactly the payload the report needs.
    //
    // A NON-literal argument is refused rather than degraded: `Partiality::Declared` carries a
    // `&'static str` so the message costs nothing on the hot path, and accepting a computed
    // message here would mean either discarding it (the defect) or interning attacker-influenced
    // strings for the process lifetime. No `![…]` body in the corpus uses one, and a grammar that
    // wants a dynamic reason should say it with a declared rewrite rule instead.
    if args.len() == 1 && method_name == "expect" {
        let arg = args
            .iter()
            .next()
            .expect("an `.expect(_)` call with args.len() == 1 has a first argument");
        return Some(match arg {
            Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(_), .. }) => syn::parse_quote! {
                ::mettail_runtime::Declarable::declared((#recv), #arg)?
            },
            other => {
                let rendered = quote!(#other).to_string();
                let message = format!(
                    "`.expect({rendered})` inside a `![…]` body needs a STRING LITERAL argument. \
                     The message is carried into the run report as \
                     `mettail_runtime::Partiality::Declared`, which holds a `&'static str`; a \
                     computed message would have to be discarded, and discarding declared failure \
                     messages is the defect this rewrite exists to close."
                );
                syn::parse_quote! { compile_error!(#message) }
            },
        });
    }

    // `.unwrap()` — same demotion, but the author declared no message. `Partiality::Unreported`
    // records precisely that: the body declined and stated no reason. The silence is the finding,
    // so it is still a DECLINE (reported), not a structural deferral.
    if args.is_empty() && method_name == "unwrap" {
        return Some(syn::parse_quote! {
            ::mettail_runtime::Declarable::unwrapped((#recv))?
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
    // Rewriting `<recv>.eval()` → `not_reduced((<recv>).try_eval())?` makes
    // user grammar code Var-safe by construction. The enclosing safeify
    // closure returns `Result<_, Partiality>`, so `?` short-circuits on
    // Var-bearing terms — evidence-driven rule-out per the
    // preserve-all-derivations mandate (P3: try_eval=None IS evidence the term
    // didn't reduce). The arm whose `.eval()` short-circuits simply doesn't
    // contribute its term to the result; other alts whose sub-terms ARE reduced
    // contribute normally.
    //
    // ★ THIS IS THE STRUCTURAL CASE, and it is the one the whole partition
    // turns on. `Partiality::NotReduced` says "not YET" — a different,
    // already-declared rule may still fire on this redex — so it DEFERS and is
    // deliberately NOT recorded as a decline. Without this distinction a term
    // that fails to fold because an operand is still a redex (a free variable,
    // an unreduced child) would be reported as though an operation had refused
    // it, and every non-firing rule in the corpus would look like a finding.
    if args.is_empty() && method_name == "eval" {
        return Some(syn::parse_quote! {
            ::mettail_runtime::partiality::not_reduced((#recv).try_eval())?
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
    fn wraps_in_result_closure_and_adapts_to_option_for_the_evaluator_lanes() {
        let expr: Expr = syn::parse_str("a + b").expect("parse");

        // The REPORTING form keeps the reason channel.
        let reported = normalise(safeify_and_wrap_reported(&expr));
        assert!(reported.contains("Result"), "expected Result wrapper: {reported}");
        assert!(reported.contains("Partiality"), "expected Partiality error: {reported}");
        // The wrapper uses `Lift(...).lift()` (LiftPlain trait) rather than a
        // literal `Ok(...)` — it works for Result<T, Partiality>, Option<T> and plain T.
        assert!(reported.contains("Lift"), "expected Lift wrapper: {reported}");
        assert!(reported.contains(". lift ()"), "expected .lift() call: {reported}");
        assert!(reported.contains("safe_add"), "expected safe_add in body: {reported}");

        // The EVALUATOR form is the same rewrite with the reason dropped at the boundary.
        let optioned = normalise(safeify_and_wrap(&expr));
        assert!(
            optioned.contains("Result :: ok"),
            "the Option-shaped lanes adapt with `Result::ok`, so the reason is computed and \
             dropped at the CONSUMER rather than never computed: {optioned}",
        );
        assert!(optioned.contains("safe_add"), "expected safe_add in body: {optioned}");
    }

    /// ★★ THE MESSAGE SURVIVES. `#100` rewrote `.expect(msg)` to a bare `(recv)?` and
    /// discarded `msg`; three Calculator fold bodies lost their declared reasons that way.
    #[test]
    fn expect_carries_the_authors_message_instead_of_discarding_it() {
        let out = safeify_str(r#"m.get(&k).cloned().expect("get: key not found")"#);
        assert!(
            out.contains("declared"),
            "`.expect(LIT)` must demote through `Declarable::declared`, not a bare `?`: {out}",
        );
        assert!(
            out.contains("\"get: key not found\""),
            "★ the author's message must appear VERBATIM in the emitted code — that is the \
             whole repair: {out}",
        );
        // The three real Calculator sites, by name.
        for message in
            ["ElemList: invalid index", "DeleteList: invalid index", "get: key not found"]
        {
            let src = format!(r#"x.expect("{message}")"#);
            let emitted = safeify_str(&src);
            assert!(
                emitted.contains(message),
                "Calculator's `{message}` must reach the generated code: {emitted}",
            );
        }
    }

    /// A NON-literal `.expect(…)` argument is REFUSED at expansion time. Degrading it would
    /// mean discarding a declared message, which is the defect being closed.
    #[test]
    fn a_non_literal_expect_message_is_refused_rather_than_dropped() {
        let out = safeify_str("x.expect(&make_message(n))");
        assert!(
            out.contains("compile_error"),
            "a computed `.expect(…)` message must fail the build, not vanish: {out}",
        );
        assert!(
            out.contains("STRING LITERAL"),
            "the refusal must say what to write instead: {out}",
        );
    }

    /// `.unwrap()` declares no message, and `Unreported` says exactly that — still a decline.
    #[test]
    fn unwrap_demotes_to_an_unreported_decline() {
        let out = safeify_str("xs.first().unwrap()");
        assert!(
            out.contains("unwrapped"),
            "`.unwrap()` must demote through `Declarable::unwrapped`: {out}",
        );
    }

    /// ★ THE STRUCTURAL CASE: `.eval()` becomes a DEFERRAL, never a decline. This is the
    /// control that keeps "an operand is still a redex" out of the decline records.
    #[test]
    fn eval_demotes_to_a_structural_not_reduced_deferral() {
        let out = safeify_str("n.as_ref().eval()");
        assert!(
            out.contains("not_reduced"),
            "`.eval()` must demote through `partiality::not_reduced` so an unreduced child \
             DEFERS instead of being recorded as a semantic decline: {out}",
        );
        assert!(out.contains("try_eval"), "expected try_eval in {out}");
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
