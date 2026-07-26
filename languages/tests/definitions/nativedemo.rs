// Task #11 (extended 2026-07-26): as a library module this definition inherited
// `languages/src/lib.rs`'s crate-level `#![allow(unused_imports, ...)]`. A `#[path]`-included
// module inherits nothing, and each consumer exercises a different slice of the generated
// surface (the parser, the codegen helpers, or neither), so `dead_code` / `unused_imports`
// are expected here rather than a signal. They are allowed at the definition -- the one place
// every consumer shares -- instead of being re-allowed at each `#[path]` site.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Stage 3e demonstration language: a minimal integer calculator whose ONLY reducing rule is a
// NATIVE SYSTEM PROCESS — the exponentiation `PowInt(a, b) ~> a^b` (`a "^" b`, a `![…] fold` HOL
// term). Unlike `+`/`-`/`==` (which the Rho scalar-contract path lowers to an in-Rho `NativeFold`),
// the `^` operator has no scalar contract, so it is REJECTED by the scalar lowering and classified
// as a `RhoNetRuleKind::NativeSystemProcess` (confirmed by `rholang-codegen`'s backend fixtures:
// `PowInt`/`AddBigInt` → `RhoNativeSystemProcess`). Its value is therefore computed by a TRUSTED
// native handler (the host's Dovetail `![a.pow(b as u32)] fold` body — model-b), not by an in-Rho
// scalar contract.
//
// This is the FIRST bundled language shape that exercises the in-Rho NATIVE-SYSTEM-PROCESS firing
// path (Stage 3e) end-to-end: SwapDemo has only a base rewrite, AcDemo only an AC rewrite, CtxDemo
// only a contextual join, LambdaDemo only a binder/β-substitution. A clean `^` redex isolates the
// native-dispatch family (D2(e)): the host matches `PowInt(a, b)` AND computes the native value via
// its trusted `fold` handler, and the reduced value reflects to a ground σ that the flat dispatch
// receiver `for (result, out <- c) { out!(result) }` fires as `⟦value⟧`.
//
// Promoted to a generated `language!` (exactly like `swapdemo`/`acdemo`/`ctxdemo`/`lambdademo`) so
// the full dovetail-driven Rho native σ-injection path can run end-to-end in
// `rholang-runtime/tests/rho_net_native_firing.rs`: the generated `dovetail_report_for` fires the
// `Int_PowInt` native rule (resolving the firing's CONTRACTUM — the native value the host computed),
// and the generated `rho_net_invocation_from_dovetail_to` reflects that contractum and delivers it
// on the `PowInt` dispatch channel, where the installed `NativeSystemProcessRewrite` receiver
// forwards it on `@out`.
//
// The redex `2 ^ 3` reduces to `8` (an `Int::NumLit(8)` leaf whose reflected image is the ground
// `NumLit(8)` term), and `2 ^ 3 ≠ 8` structurally, so a positive OUT observation is non-vacuous
// evidence the native system process fired as a COMM with the value the trusted handler computed.
//
// Deliberately minimal (a single native operator, no congruence closures): a ROOT-rooted `^` redex
// matches `PowInt` at the root, so no congruences are needed to isolate INV-3 for the native
// family — exactly as SwapDemo/LambdaDemo drop congruences to isolate their family.
language! {
    name: NativeDemo,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `nativedemo_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_nativedemo_*.rs`, whose `use mettail_languages::nativedemo::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/nativedemo.rs",
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        ![i64] as Int
    },

    terms {
        PowInt . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] fold;
    },

    equations {},

    rewrites {},
}
