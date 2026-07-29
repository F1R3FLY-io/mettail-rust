// MeTTaIL Language Definitions Library
//
// This crate contains the core language definitions used across examples and the REPL.
// Each language is defined in its own module using the language! macro.

// ★ (Task #101) AUTO-TRAIT SEARCH DEPTH, not an "obligation overflow".
//
// The generated Dovetail report memoizes its compiled rule set in
// `static __DOVETAIL_COMPILED_RULES: OnceLock<CompiledRuleSet<<Lang>DovetailOp>>`, and a
// `static` requires `Sync`. Proving `<Lang>DovetailOp: Send + Sync` walks the op enum's payload
// types, which for Rholang means nineteen mutually recursive AST categories, each reaching the
// others through `Scope<Binder<String>, Arc<Cat>>` and `Arc<CatLit>` wrappers. That graph is
// FINITE and acyclic in the auto-trait sense — every obligation terminates — but it is deep, and
// rustc's default `recursion_limit` of 128 is a fixed SEARCH BOUND on obligation depth, not a
// statement about the program.
//
// Measured: Rholang sat immediately under that bound. Task #101 gave ordered collection fields a
// labelled carrier (`FieldSeq<Elem>(Vec<Elem>)`, so a fold operand has an inverse to bind
// through), which adds `Vec<Name>` / `Vec<ForRow>` / `Vec<InputBind>` nodes — one extra level
// each on paths that were already at 128 — and the search reported
// `E0275: overflow evaluating the requirement Arc<WriteZipperLit>: Send`. Reproducibly, and
// UNIT-DEPENDENTLY: the same source type-checked in `cargo build -p languages --lib` and
// overflowed in `cargo check --workspace --all-targets`, because dev-dependency feature
// unification changes the dependency graph and with it the solver's query order. A bound that
// close is a latent build break regardless of #101.
//
// Raising it is rustc's own documented remedy (the diagnostic emits exactly this suggestion) and
// costs nothing but compiler search headroom: it admits no program that was previously rejected
// as ILL-TYPED, only ones that were previously abandoned as too deep to search.
//
// ⚠ It belongs HERE and only here. The bound applies to the crate in which the `static` is
// expanded, and Rholang — much the largest language in the tree — is a module of this crate.
// The test-hosted fixture grammars under `languages/tests/definitions/` are an order of
// magnitude smaller and are nowhere near the default.
#![recursion_limit = "256"]
#![allow(
    clippy::cloned_ref_to_slice_refs,
    clippy::type_complexity,
    unused_imports, // generated parser code may include unused imports
)]

// Task #11 (extended 2026-07-26): `AcDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/acdemo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "ac-demo")]
// pub mod acdemo;
// Stage AC2b: the bag-TRANSFORMING (nested-bag RHS) AC firing demonstration language.
// Task #11 (extended 2026-07-26): `AcBagDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/acbagdemo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "ac-bag-demo")]
// pub mod acbagdemo;
// Stage 4 S-AC (AC3): the NON-LINEAR `{x, x, ...rest}` bare-var AC firing demonstration language.
// Task #11 (extended 2026-07-26): `NlAcDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/nlacdemo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "nl-ac-demo")]
// pub mod nlacdemo;
// Stage 3d: the Ambient-calculus `OpenRule` STRUCTURAL non-linear AC firing demonstration language.
// Task #11 (extended 2026-07-26): `AmbDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/ambdemo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "amb-demo")]
// pub mod ambdemo;

// Task #11 (extended 2026-07-26): `AmbNewDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/ambnewdemo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "amb-new-demo")]
// pub mod ambnewdemo;
// Stage 4 (Ambient In/Out): the DEPTH-2 NESTED structural non-linear AC firing demonstration language
// (the Ambient-calculus `InRule`/`OutRule`), generalizing `AmbDemo`'s flat `OpenRule`.
// Task #11 (extended 2026-07-26): `InOutDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/inoutdemo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "in-out-demo")]
// pub mod inoutdemo;
#[cfg(feature = "ambient")]
pub mod ambient;
// Task #11 (extended 2026-07-26): `AppSubst` is a binder-calculus FIXTURE (the generality
// gate for macro-codegen extension E1), not a production language, so it moved to
// `languages/tests/definitions/appsubst.rs`. `languages/src/` is production-only.
// #[cfg(feature = "appsubst")]
// pub mod appsubst;
#[cfg(feature = "calculator")]
pub mod calculator;
// GSLT omnibus conformance specs (2026-07-27, USER ruling: "The language specs from the
// omnibus paper may stay in `languages/src/` — they may be considered production specs").
// `Json` (L1), `Monoid` (L2), `Turing` (L9) and `Pi` (L11) were declared inside their own
// test binaries as `languages/tests/omnibus_*.rs`, which made them reachable from nothing
// but that one binary. They are library modules now, like every other production spec, and
// their conformance suites are `languages/tests/{json,monoid,pi,turing}.rs`.
#[cfg(feature = "json")]
pub mod json;
// Task #11 (extended 2026-07-26): the Class-2 / Class-3 collection FIXTURE grammars are
// not production languages, so they moved to `languages/tests/definitions/`.
// `languages/src/` is production-only. Consumers `#[path]`-include the definition files
// directly; each definition's DESIGNATED HOST test binary invokes its generated suite.
// #[cfg(feature = "class2hashmapsmoke")]
// pub mod class2hashmapsmoke;
// #[cfg(feature = "class2multi")]
// pub mod class2multi;
// #[cfg(feature = "class2optsmoke")]
// pub mod class2optsmoke;
// #[cfg(feature = "class2smoke")]
// pub mod class2smoke;
// #[cfg(feature = "class3multi")]
// pub mod class3multi;
// #[cfg(feature = "class3opt")]
// pub mod class3opt;
// Stage 3b: the canonical single-receive Rholang COMMUNICATION rule (non-linear AC firing).
// Task #11 (extended 2026-07-26): `CommDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/commdemo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "comm-demo")]
// pub mod commdemo;
// Stage 3a: the unary-congruence (contextual join) demonstration language.
// Task #11 (extended 2026-07-26): `CtxDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/ctxdemo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "ctx-demo")]
// pub mod ctxdemo;
// Stage 4 S-contextual (sub-slice 2): the 2-ARY-congruence (n-hole contextual join) demonstration.
// Task #11 (extended 2026-07-26): `BiCongDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/bicongdemo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "bicong-demo")]
// pub mod bicongdemo;
// Stage 3c: the untyped λ-calculus binder/β-substitution demonstration language.
// Task #11 (extended 2026-07-26): `LambdaDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/lambdademo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "lambda-demo")]
// pub mod lambdademo;
// Stage 3e (rho-native): the native-system-process (`![…] fold` PowInt) firing demonstration.
// Task #11 (extended 2026-07-26): `NativeDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/nativedemo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "native-demo")]
// pub mod nativedemo;
// Stage 3f (rho-native): the native-scalar-fold (`![…] fold` AddInt) firing demonstration.
// Task #11 (extended 2026-07-26): `NativeFoldDemo` is a DEMONSTRATION language definition;
// it moved to `languages/tests/definitions/nativefolddemo.rs`. `languages/src/` is
// production-only. Consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "native-fold-demo")]
// pub mod nativefolddemo;
// PIECE 3: keyword-reservation OPT-OUT fixture (Fortran-style full ambiguity).
// Task #11 (extended 2026-07-26): a keyword-reservation FIXTURE, not a production language;
// it moved to `languages/tests/definitions/fortran_model.rs`.
// #[cfg(feature = "fortran_model")]
// pub mod fortran_model;
// Task #11 (extended 2026-07-26): `GuardedRho` is a rough PROTOTYPE grammar (USER: "GuardedRho
// was a rough prototype to test the where clause and guards block"), not a production
// language, so it moved to `languages/tests/definitions/guarded_rho.rs`.
// #[cfg(feature = "guarded-rho")]
// pub mod guarded_rho;
#[cfg(feature = "lambda")]
pub mod lambda;
// GSLT omnibus L2 — see the `json` note above.
#[cfg(feature = "monoid")]
pub mod monoid;
// Task #11 (extended 2026-07-26): `LedTest` is the LED-delegation FIXTURE grammar; it moved
// to `languages/tests/definitions/led_test.rs`.
// #[cfg(feature = "led-test")]
// pub mod led_test;
// Task #11 (extended 2026-07-26): `GuardOptSmoke` is the A-11 site-2 ParsePredicate FIXTURE;
// it moved to `languages/tests/definitions/guardoptsmoke.rs`.
// #[cfg(feature = "guardoptsmoke")]
// pub mod guardoptsmoke;
// Task #11: `OptSmoke` is a TEST language definition; it moved to
// `languages/tests/definitions/optsmoke.rs`. `languages/src/` is production-only.
// #[cfg(feature = "optsmoke")]
// pub mod optsmoke;
// Task #11 (extended 2026-07-26): `RefinementSmoke` is the refinement-predicate codegen
// FIXTURE; it moved to `languages/tests/definitions/refinementsmoke.rs`.
// #[cfg(feature = "refinementsmoke")]
// pub mod refinementsmoke;
// Task #11 (extended 2026-07-26): the keyword-reservation ENABLED (`auto`) twin of
// `FortranModel`; it moved to `languages/tests/definitions/reserved_model.rs`.
// #[cfg(feature = "reserved_model")]
// pub mod reserved_model;
// GSLT omnibus L11 — see the `json` note above.
#[cfg(feature = "pi")]
pub mod pi;
#[cfg(feature = "rholang")]
pub mod rholang;
// GSLT omnibus L9 — see the `json` note above.
#[cfg(feature = "turing")]
pub mod turing;
// Task #11 (extended 2026-07-26): `SwapDemo` is a DEMONSTRATION grammar, not a production
// language, so it moved to `languages/tests/definitions/swapdemo.rs`. `languages/src/` is
// production-only; consumers `#[path]`-include the definition file directly.
// #[cfg(feature = "swap-demo")]
// pub mod swapdemo;

// Composition test languages — module order matters for proc-macro registry population.
// fragments and base_lang must compile before their consumers.
#[cfg(feature = "composition")]
pub mod composition;

// Re-export composition language modules at crate root for generated test file access.
// Generated test files use `mettail_languages::{name}::*` which requires crate-root modules.
#[cfg(feature = "composition")]
pub use composition::base_lang as basemath;
#[cfg(feature = "composition")]
pub use composition::extended_lang as extmath;
#[cfg(feature = "composition")]
pub use composition::grammar_import_lang as importedmath;
#[cfg(feature = "composition")]
pub use composition::mixed_lang as mixedmath;
// Task #11 (extended 2026-07-26): `GuardedRho` is test-hosted, so there is no library module
// to alias. Consumers `#[path]`-include `tests/definitions/guarded_rho.rs` and name the module
// `guardedrho` at the include site (the macro derives that name from the language NAME, which
// is what the `guardedrho_generated_tests!` wrapper uses).
// #[cfg(feature = "guarded-rho")]
// pub use guarded_rho as guardedrho;
// Task #11 (extended 2026-07-26): `LedTest` is test-hosted now, so there is no library
// module to alias. Consumers `#[path]`-include `tests/definitions/led_test.rs` and name the
// module `ledtest` at the include site (the macro derives the alias from the language NAME,
// which is what the generated `simulate_ledtest` binary and the wrapper both use).
// #[cfg(feature = "led-test")]
// pub use led_test as ledtest;

// Note: Different languages may export types with the same names (e.g., Proc, Term)
// Users should import from specific modules to avoid ambiguity:
//   use mettail_languages::rholang::*;
//   use mettail_languages::ambient::*;
//   use mettail_languages::lambda::*;

/// Shared, deterministic input generators for the parser benchmarks (`languages/benches/*`).
/// Compiled once here so its `pub` helpers are reachable library API — this is what keeps the
/// per-bench dead-code analysis from firing without any `#[allow(dead_code)]`.
pub mod bench_common;
