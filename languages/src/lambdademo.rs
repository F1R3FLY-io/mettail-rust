#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Stage 3c demonstration language: an untyped λ-calculus whose β-reduction
// `App(Lam(^x. b), a) ~> subst(b, x := a)` (written `(App (Lam fun) arg) ~> (eval fun arg)`
// in the DSL — the `eval` operator IS the capture-avoiding substitution) is a BASE rewrite
// over a binder LHS with a substitution RHS.
//
// This is the FIRST bundled language shape that exercises the in-Rho BINDER firing path
// (Stage 3c) end-to-end: SwapDemo has only a base rewrite, AcDemo only an AC rewrite, CtxDemo
// only a contextual join. A clean β-redex isolates the binder/substitution family (D2(d)):
// the host (Dovetail, model-b) does the matching AND the capture-avoiding substitution, and
// the reduced term reflects to a ground σ that the flat σ-receiver fires as `⟦R⟧σ`.
//
// Promoted to a generated `language!` (exactly like `swapdemo`/`acdemo`/`ctxdemo`) so the full
// dovetail-driven Rho substitution σ-injection path can run end-to-end in
// `rholang-runtime/tests/rho_net_beta_firing.rs`: the generated `dovetail_report_for` fires
// `Beta` (resolving its σ AND the firing's CONTRACTUM — the reduced term the host computed),
// and the generated `rho_net_invocation_from_dovetail_to` reflects that contractum at the scope
// variable's σ slot and delivers it on the `Beta` σ-receiver channel, where the installed
// `SubstRewrite` σ-receiver forwards it on `@out`.
//
// The redex `App(Lam(^x. f(x)), A)` reduces to `f(A)`, and `App(Lam(^x. f(x)), A) ≠ f(A)`, so a
// positive OUT observation is non-vacuous evidence β-reduction fired as a COMM with the reduct
// Dovetail computed.
//
// Deliberately minimal (only the `Beta` base rewrite, no congruence closures): a ROOT-rooted
// β-redex matches `Beta` at the root, so no `AppCong`/`LamCong` congruences are needed to
// isolate INV-3 for the binder family — exactly as SwapDemo drops congruences to isolate the
// base rewrite. (The full `mettail_languages::lambda` fixture carries the congruences.)
language! {
    name: LambdaDemo,

    options {
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Term
    },

    terms {
        Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
        App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
        F . a:Term |- "f" "(" a ")" : Term ;
        A . |- "A" : Term ;
    },

    equations {},

    rewrites {
        Beta . |- (App (Lam fun) arg) ~> (eval fun arg) ;
    },
}
