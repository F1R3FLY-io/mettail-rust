// Task #11 (extended 2026-07-26): as a library module this definition inherited
// `languages/src/lib.rs`'s crate-level `#![allow(unused_imports, ...)]`. A `#[path]`-included
// module inherits nothing, and each consumer exercises a different slice of the generated
// surface (the parser, the σ-injection, or neither), so `dead_code` / `unused_imports` are
// expected here rather than a signal. They are allowed at the definition — the one place
// every consumer shares — instead of being re-allowed at each `#[path]` site.
#![allow(
    dead_code,
    non_local_definitions,
    unused_imports,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Stage 3f demonstration language: a minimal integer calculator whose ONLY reducing rule is a
// NATIVE SCALAR FOLD — the addition `AddInt(a, b) ~> a + b` (`a "+" b`, a `![a + b] fold` HOL
// term). Unlike `^` (which has no in-Rho scalar contract and is REJECTED by the scalar lowering,
// so it is classified as a `RhoNetRuleKind::NativeSystemProcess` — Stage 3e / `nativedemo.rs`),
// the `+` operator DOES lower to an in-Rho scalar contract, so it is classified as a
// `RhoNetRuleKind::NativeFold` (the scalar-fold family, D2(f) / D3). Its value `a + b` is the
// directed COMPUTE of a native fold — the fold-vs-equation criterion (D3, INV-9) — so per the
// campaign it fires as a COMM (motion changing a CLTS barb), NOT compile-time congruence.
//
// This is the FIRST bundled language shape that exercises the in-Rho NATIVE-SCALAR-FOLD firing
// path (Stage 3f) end-to-end: SwapDemo has only a base rewrite, AcDemo only an AC rewrite, CtxDemo
// only a contextual join, LambdaDemo only a binder/β-substitution, NativeDemo only a native SYSTEM
// PROCESS (`^`, no scalar contract). A clean `+` redex isolates the native-scalar-fold family
// (D2(f)): the host matches `AddInt(a, b)` AND computes the reduced value `a + b` via its trusted
// `fold` handler (model-b), and the reduced value reflects to a ground σ that a flat dispatch
// receiver `for (result, out <- c) { out!(result) }` fires as `⟦value⟧` — the SAME contractum lane
// Stage 3e's native SYSTEM PROCESS uses (`NativeSystemProcessRewrite`), now un-skipped for the
// scalar-fold family (`NativeFoldRewrite`).
//
// Promoted to a generated `language!` (exactly like `swapdemo`/…/`nativedemo`) so the full
// dovetail-driven Rho native σ-injection path can run end-to-end in
// `rholang-runtime/tests/rho_net_native_fold_firing.rs`: the generated `dovetail_report_for` fires
// the `Int_AddInt` native-fold rule (resolving the firing's CONTRACTUM — the reduced value the host
// computed), and the generated `rho_net_invocation_from_dovetail_to` reflects that contractum and
// delivers it on the `AddInt` dispatch channel, where the installed `NativeFoldRewrite` receiver
// forwards it on `@out`.
//
// The redex `2 + 3` reduces to `5` (an `Int::NumLit(5)` leaf whose reflected image is the ground
// `NumLit(5)` term), and `2 + 3 ≠ 5` structurally, so a positive OUT observation is non-vacuous
// evidence the native scalar fold fired as a COMM with the value the host computed.
//
// Deliberately minimal (a single native scalar operator, no congruence closures): a ROOT-rooted
// `+` redex matches `AddInt` at the root, so no congruences are needed to isolate INV-3 for the
// native-scalar-fold family — exactly as SwapDemo/LambdaDemo/NativeDemo drop congruences to isolate
// their family.
language! {
    name: NativeFoldDemo,

    options {
        emit_simulator: false,
        emit_blockly: false,
        // Task #11 (extended 2026-07-26): this is a DEMONSTRATION language, not
        // production, so it lives in `languages/tests/definitions/` rather than in
        // the library. The key tells the macro to emit the generated suite inline
        // (an opt-in `nativefolddemo_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_nativefolddemo_*.rs`, whose
        // `use mettail_languages::nativefolddemo::*;` header cannot resolve once the
        // definition has left the library.
        hosted_in: "tests/definitions/nativefolddemo.rs",
    },

    types {
        ![i64] as Int
    },

    terms {
        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
    },

    equations {},

    rewrites {},
}
