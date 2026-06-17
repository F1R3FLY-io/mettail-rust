# Macro-Generated Per-Language Numeric-Cast Adapters

**Status:** design red-teamed (2 independent critics, round 1; blockers resolved below), ready to implement.
**Supersedes the hand-written adapter layer in** `languages/numeric_dispatch.rs` (to be deleted).
**Companion:** [`numeric-casting.md`](numeric-casting.md) (the numeric-cast *semantics*; unchanged here).

## 1. Motivation

The native-fold campaign (cast-eval gap closure) reduces numeric casts — RhoCalc
`int(a, w) : Proc`, Calculator `int(a, w) : Int`, etc. — by calling a small per-language
**adapter** that translates the language's concrete `Proc` AST to/from the
language-agnostic numeric pipeline in `mettail_runtime::numeric_cast_dispatch`.

Today that adapter is **hand-written and duplicated per language** in
`languages/numeric_dispatch.rs`: a `calc_*` family (`CalcProc`) and a `rho_*` family
(`RhoProc`). Adding any new language with numeric casts would require yet another
hand-written family. The project mandate is to support *theoretically any language's
grammar*, so this per-language glue must be **macro-generated from the language spec**.

The general numeric *computation* (`numeric_try_*`, `int_bin_pipeline_*`, …) is already
language-agnostic and is **not** touched. Only the **adapter layer** is generalized.

## 2. The three layers (and what changes)

| Layer | Location | Change |
|---|---|---|
| **A. Shared math/pipeline** | `runtime/src/numeric_cast.rs`, `runtime/src/numeric_cast_dispatch.rs` (`NumericInput`, `numeric_try_*`, `*_pipeline_*`) | **none** |
| **B. Per-language adapter** | hand-written `languages/numeric_dispatch.rs` | **deleted**; replaced by generic reductions in `mettail_runtime` + macro-generated trait impls |
| **C. Macro emission** | `macros/src/gen/…` emits each fold body verbatim into its consumer | extend one classifier; add an adapter-impl generator |

**Design thesis:** move the adapter *logic* into generic `mettail_runtime` functions
keyed on three traits, and have the macro generate only the mechanical, spec-derived
**trait impls** per language. A new language then writes **zero** numeric-cast glue.

## 3. Trait surface — `runtime/src/numeric_cast_adapter.rs` (new module)

Three traits in `mettail_runtime`. Impls are generated **into each language crate's
module** — sound under the orphan rule because the `Self` type (`Proc`/`Int`/`&Int`) is
local to `mettail-languages`; the trait is foreign. (`&Int` is allowed because `&T` is
`#[fundamental]` and `T` is local — already proven by the compiling `impl CastWidth for
&RhoInt`.)

```rust
/// Width `m` of a cast (`int(a, m)`). Relocated from languages/numeric_dispatch.rs:20
/// — MUST move to the runtime BEFORE deleting that file (it defines the trait).
pub trait CastWidth { fn into_width_i64(self) -> Option<i64>; }
impl CastWidth for i32 { fn into_width_i64(self) -> Option<i64> { Some(self as i64) } }
impl CastWidth for i64 { fn into_width_i64(self) -> Option<i64> { Some(self) } }

/// Map a reduced numeric `Proc` to a borrowed NumericInput; None ⇒ non-numeric/not-reduced.
pub trait ProcToNumericInput {
    fn to_numeric_input(&self) -> Option<NumericInput<'_>>;
    #[inline] fn peel_numeric_elem(&self) -> &Self { self }      // indexed-collection peel; default identity
    #[inline] fn as_numeric_str(&self) -> Option<&str> { None }  // string fast-path
    #[inline] fn as_evaluable_bigrat(&self) -> Option<CanonicalBigRat> { None } // float-bin only
    #[inline] fn as_int_bin(&self)   -> Option<(&Self, i64)> { None } // nested same-op recursion
    #[inline] fn as_float_bin(&self) -> Option<(&Self, i64)> { None }
    #[inline] fn as_fixed_bin(&self) -> Option<(&Self, i64)> { None }
}

/// Build an OBJECT-output result `Proc` (or the language's Err). Implemented ONLY for
/// non-native-output languages (RhoCalc). Native-output languages (Calculator) never
/// implement this — their reductions return the native scalar and DEFER (None) on failure.
pub trait CastResult: Sized {
    fn err() -> Self;
    fn from_int(n: i64) -> Self;  fn from_uint(n: u32) -> Self;
    fn from_float(f: CanonicalFloat64) -> Self;  fn from_fixed(fp: CanonicalFixedPoint) -> Self;
    fn from_bigint(n: CanonicalBigInt) -> Self;  fn from_bigrat(r: CanonicalBigRat) -> Self;
}
```

`NumericInput` (verified `numeric_cast_dispatch.rs:18-27`, `#[derive(Clone, Copy)]`):
`I32(i32) | I64(i64) | U32(u32) | BigInt(&BigInt) | BigRat(&Ratio<BigInt>) |
Fixed(&CanonicalFixedPoint) | F64(f64)`.

## 4. Generic reductions — two families (the defer-vs-Err split is load-bearing)

Calculator casts are **native-output** (`: Int`/`: BigInt`/…): the body returns
`Option<scalar>`; `None` ⇒ the redex **defers** (stays unreduced). RhoCalc casts are
**object-output** (`: Proc`): the body returns `Proc`, with `Proc::Err` on a bad cast.
These are TWO families that share the math layer but differ in failure model and width:

```rust
// ── native-output (Option, defer-on-None). Calculator Int = i32, so it uses *_i32. ──
pub fn numeric_int_bin_i32<P: ProcToNumericInput, W: CastWidth>(a: &P, w: W) -> Option<i32>;
pub fn numeric_int_bin_i64<P: ProcToNumericInput, W: CastWidth>(a: &P, w: W) -> Option<i64>; // RhoCalc Int = i64 (used by proc_int_bin)
pub fn numeric_uint_bin_u32<P: ProcToNumericInput, W: CastWidth>(a: &P, w: W) -> Option<u32>;
pub fn numeric_float_bin<P: ProcToNumericInput, W: CastWidth>(a: &P, w: W) -> Option<CanonicalFloat64>;
pub fn numeric_fixed_bin<P: ProcToNumericInput, W: CastWidth>(a: &P, w: W) -> Option<CanonicalFixedPoint>;
pub fn numeric_bigint_unary<P: ProcToNumericInput>(a: &P) -> Option<CanonicalBigInt>;
pub fn numeric_bigrat_unary<P: ProcToNumericInput>(a: &P) -> Option<CanonicalBigRat>;

// ── object-output (Proc, Err-on-failure). RhoCalc only; needs CastResult. ──
pub fn proc_int_bin<P: ProcToNumericInput + CastResult, W: CastWidth>(a: &P, w: W) -> P
    { numeric_int_bin_i64(a, w).map_or_else(P::err, P::from_int) }
pub fn proc_uint_bin<P,W>(a:&P,w:W)->P  { numeric_uint_bin_u32(a,w).map_or_else(P::err,P::from_uint) }
pub fn proc_float_bin<P,W>(a:&P,w:W)->P { numeric_float_bin(a,w).map_or_else(P::err,P::from_float) }
pub fn proc_fixed_bin<P,W>(a:&P,w:W)->P { numeric_fixed_bin(a,w).map_or_else(P::err,P::from_fixed) }
pub fn proc_bigint_unary<P>(a:&P)->P    { numeric_bigint_unary(a).map_or_else(P::err,P::from_bigint) }
pub fn proc_bigrat_unary<P>(a:&P)->P    { numeric_bigrat_unary(a).map_or_else(P::err,P::from_bigrat) }
```

Each `numeric_*` body preserves the hand-written control flow **and order** exactly
(verified per-arity against `languages/numeric_dispatch.rs`): (1) `peel_numeric_elem`,
(2) `as_numeric_str` → the string fast-path fn, (3) the nested same-op recursion via
`as_int_bin`/`as_float_bin`/`as_fixed_bin` (present only on the arities that had it),
(4) `as_evaluable_bigrat` (float-bin only), (5) `to_numeric_input` fallthrough → the
typed pipeline. **Exact string fast-path fns** (verified — note float/fixed/bigrat have
NO `*_decimal_str_*`): `int_bin_pipeline_decimal_str_{i32,i64}`,
`uint_bin_pipeline_decimal_str_u32`, `float_bin_pipeline_parse_f64`,
`fixed_bin_pipeline_numeric_str`, `bigint_unary_pipeline_decimal_str`,
`bigrat_unary_pipeline_numeric_str`.

The free-var defer (`int(x,8)` stays unreduced) is enforced by the **dispatcher's
fold-readiness gate** (`typed_report.rs` `__class_is_fold_value`/object-param gate),
*before* the body runs — unchanged. `proc_*`'s `map_or_else(P::err, …)` only distinguishes
good-cast vs bad-cast, faithfully reproducing `rho_proc_*`.

The migrated fold bodies and generated impls reference the **flat crate-root re-export**
`mettail_runtime::proc_int_bin` / `mettail_runtime::numeric_int_bin_i32` (NOT
`mettail_runtime::numeric_cast::…` — that module is private; a qualified path is E0603).

## 5. What the macro generates, per language

For a language `L` whose spec has numeric-cast cast rules (`CastInt . k:Int |- k : Proc;`,
…) and numeric-cast fold rules (`IntBinProc . a:Proc, w:Int |- "int"(a,w) : Proc ![{
mettail_runtime::proc_int_bin(&a, w) }] fold;`), the macro emits into `L`'s module:

1. `impl CastWidth for Int` + `impl CastWidth for &Int` — from the width category's literal
   variant + native type (`NumLit`→`i64`/`i32`); preserves the `_ => None` (incl. `CastErr*`→None) arm.
2. `impl ProcToNumericInput for Proc` — `to_numeric_input` with one arm per `Cast*` rule
   (`(ProcVariant, InnerCat, LiteralVariant, NativeType)` → `NumericInput` arm, via the
   fixed native-type→variant table) **plus** the language's *actual* nested-redex arms and
   `as_int_bin`/`as_float_bin`/`as_fixed_bin`/`as_evaluable_bigrat`/`as_numeric_str`/
   `peel_numeric_elem` overrides — derived from that language's fold-rule AST shapes (calc
   nests `ProcFixed(FixedBin)`, rho has top-level `FixedBinProc`; the generated arms encode
   each shape from the spec).
3. `impl CastResult for Proc` — **only** if `L` has object-output numeric casts; `from_*`
   uses the per-type literal label via `generate_literal_label` (`from_int`→`NumLit`,
   `from_float`→`FloatLit`, `from_fixed`→`FixedLit`, `from_bigrat`→`RatLit`; all
   `Arc::new`), `err()` = `L`'s nullary `Err` constructor.

**Recognition (non-brittle):** a fold is a numeric cast iff its body (a parsed
`syn::Expr`, `ast/src/types.rs:188`) is a call whose final path segment ∈ the fixed set of
13 generic fn names. The macro keys off the actual runtime symbol invoked — the single
source of truth — not constructor-name heuristics.

**Gating predicate (precise — NOT `needs_typed_fold_path`, which is true for both langs):**
emit `L`'s adapter impls (and `CastResult`) **ungated** iff `L` has at least one
**native-output** numeric cast (its body is consumed by the always-emitted `eval.rs`
native-handler path in the default build); emit them under `#[cfg(feature =
"dovetail-codegen")]` iff **all** of `L`'s numeric casts are **object-output** (consumed
only by the typed dispatcher, which is itself `dovetail-codegen`-gated). ⇒ Calculator:
ungated, no `CastResult`. RhoCalc: `dovetail-codegen`-gated, with `CastResult`. This
supersedes the interim hand-gate `#[cfg(all(rhocalc, dovetail-codegen))]`.

## 6. The one classifier patch (the flagged hazard — red-team blocker 1)

`body_returns_option` (`macros/src/gen/runtime/dovetail_report/typed_report.rs:111-133`)
decides whether a fold body is `Option`-returning (→ `?`-unwrap → defer) by matching the
callee's final segment against a `try` segment. The renamed native generics
(`numeric_int_bin_i32`, …) contain no `try` → would mis-classify → E0308 in the Calculator
`dovetail-codegen` build (`Int::NumLit(Option<i32>)`). **Fix:** add a `const` allow-list of
the **7 native** fn names (`numeric_int_bin_i32/i64`, `numeric_uint_bin_u32`,
`numeric_float_bin`, `numeric_fixed_bin`, `numeric_bigint_unary`, `numeric_bigrat_unary`)
matched on the final segment ⇒ Option-returning. The **6 `proc_*`** names stay OUT (they
return `Proc`). **Do NOT touch** `eval.rs::rust_code_returns_option` — it governs only the
dead `match_arm` content (gate-only, never emitted) and the PDA `try_eval` path is
`Lift`-agnostic to `Option<T>` vs `T` (verified by the macro-side critic).

## 7. Zero-dead-code, per feature combination (the no-`allow(dead_code)` invariant)

Every generated item is gated by the cfg under which its unique consumer compiles:
- runtime generic fns are `pub` library API ⇒ never dead-code-linted.
- **default** (`all-languages`, no dovetail-codegen): Calculator adapter ungated + consumed
  by `eval.rs`; RhoCalc adapter gated out (its Proc fold bodies are not emitted on the
  `EGraph<String>`/default path — verified: that path never references `f.body`).
- **+dovetail-codegen**: RhoCalc adapter compiles + consumed by the typed dispatcher;
  Calculator adapter still consumed by both `eval.rs` and the typed path.
- single-language combos: symmetric. All five combos build with `-D warnings` (Phase 3 gate).

Generated impls reference runtime fns by **fully-qualified path** ⇒ no `use` imports to go
unused. The deleted file's `use mettail_runtime::{…}` block goes with it.

## 8. Formal impact: none

The report-compiler proofs treat the fold body as an opaque host fn `args → Option<value>`
/ `args → Proc`. This refactor preserves that contract byte-for-byte (`proc_int_bin`
returns `Proc` exactly as `rho_proc_int_bin`; `numeric_int_bin_i32` returns `Option<i32>`
exactly as `calc_try_int_bin`). `grep` over `formal/` shows zero references to the adapter.
No `.v` change; zero-admission preserved (re-verified in Phase 5).

## 9. Test plan

- Unchanged-but-must-stay-green: `languages/tests/rhocalc_dovetail_fold.rs` (6, incl.
  `free_var_arg_defers`, `bad_cast_folds_to_err`), `rhocalc_dovetail_op_enum.rs`, Calculator
  cast suites, `runtime` numeric_cast tests.
- New: `runtime/src/numeric_cast_adapter.rs` unit tests over an in-test `FakeProc`
  implementing the three traits (proves the generics work over an arbitrary `Proc` with no
  `language!`) — int overflow, string arm, bad-cast→Err, nested recursion.
- New: a macro token-test asserting the adapter impls are *generated* (and gated) for a
  minimal cast-bearing language.
- New: a third cast-bearing language fixture (prefer extending an existing math-composition
  language) proving "any language" gets numeric casts with zero hand-written glue.

## 10. Red-team resolutions (round 1)

| Blocker | Resolution |
|---|---|
| Renamed calc bodies break `body_returns_option` (E0308) | §6 allow-list in `body_returns_option` **only**; leave `eval.rs` |
| `mettail_runtime::numeric_cast::…` is a private path (E0603) | §4 flat re-export `mettail_runtime::proc_int_bin` |
| `CastWidth` trait *defined* in the deleted file (E0119/missing) | §3 relocate trait+blanket impls to runtime; delete file atomically in Phase 3 |
| calc `i32` vs rho `i64` width | §4 distinct `numeric_int_bin_i32` (calc) / `_i64` (rho) |
| calc defer-on-None vs rho `Proc::Err` | §4 two families; `CastResult`/Err rho-only; calc never routes failure through `err()` |
| per-language nested-redex AST shapes differ | §5 generated `as_*_bin`/`to_numeric_input` arms derived from each spec |

## 11. Implementation roadmap (each phase independently buildable; the build IS the convergence test)

- **P0** Add `runtime/src/numeric_cast_adapter.rs` (traits + 13 generics, exact pipeline
  names), re-export from `runtime/src/lib.rs`; `FakeProc` unit tests. Old file untouched.
  *Verify:* `cargo test -p mettail-runtime`.
- **P1** Extend `body_returns_option` (`typed_report.rs`) with the 7-native allow-list (final
  segment); macro unit assertion. *Verify:* `cargo test -p mettail-macros`.
- **P2** Add `macros/src/gen/runtime/numeric_cast_adapter.rs`
  (`generate_numeric_cast_adapter`), wire into the language aggregator
  (`macros/src/gen/runtime/language.rs`), gate per §5. Old file still present (no collision
  — new trait impls vs old free fns). *Verify:* default + `--features dovetail-codegen`
  builds; macro token test.
- **P3** Migrate fold bodies (`rhocalc.rs`→`proc_*`, `calculator.rs`→`numeric_*`); **delete**
  `languages/numeric_dispatch.rs` + its `mod` block (`lib.rs`); relocate `CastWidth`.
  *Verify:* all 5 feature combos build with `RUSTFLAGS="-D warnings"`.
- **P4** Behavior tests + the third-language fixture. *Verify:* `cargo test -p
  mettail-languages [--features dovetail-codegen]`.
- **P5** Formal zero-admission re-check + whole-workspace gate; confirm `git grep
  numeric_dispatch` empty, no new `allow(dead_code)`, root `Cargo.toml` untouched.
