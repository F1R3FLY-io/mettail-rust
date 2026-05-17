# Phase D Multi-Cat Extract — Principled Redesign

**Date**: 2026-05-17
**Branch**: `feature/wfst-architecture`
**Origin tip**: `aa75cd0` (Phase A.5 — after the regression-introducing 618e443)
**Status**: design ready; implementation begun

---

## Diagnosis: Why the Union-Extract Caused 46 Regressions

The root cause is not the multi-cat union extract per se — it's the **interaction
between all-alts seeding (D.1) and panic-prone user-action code** (`b.as_ref().eval()`)
in fold rules.

When `bool(true)` parses unambiguously as `Bool`, only `prog.bool` gets seeded; rules
that touch `Proc` (e.g., `Bool::ProcToBool`'s arms casting `Proc::ProcBigInt(n)` via
`n.as_ref().eval()`) never fire because no `Proc` is present. With multi-cat union
extract, `bool(int(3.14)) + 1` seeds **all** matching cats (`Int`, `BigInt`,
`UInt32`, `BigRat`, `Fixed`, `Float`, etc.). The `Bool::ProcToBool` rule's `match a
{ Proc::ProcBigInt(n) => ... .eval() ... }` (`calculator.rs:264`) now fires against
a partially-reduced/Var-bearing `BigInt` term, and `eval()` panics (line 5037 in
generated code). The panic aborts the whole test (no `catch_unwind` around
`prog.run()`).

The fix is **NOT** to revert to single-cat extract (loses cross-cat results,
regresses rhocalc_op tests and the new Phase-D capability), nor to add
`catch_unwind` (hides bugs, slows the hot path). The principled fix is to **make
user-action codegen Var-safe by default** — exactly as `ProcToStr` already does
(lines 5081-5103: uses `try_eval()` in every arm and falls through to
`_ => String::new()`).

---

## Recommended Approach: Hybrid (Per-Alt Seed Filter + try_eval-Safe Codegen)

### Layer 1: Codegen-time `safeify` extension

Extend `macros/src/gen/native/rust_code_rewrite.rs::safeify_methods_and_wrap` to
rewrite `<expr>.eval()` → `<expr>.try_eval()?` (parallel to existing
`.unwrap()` → `(<expr>)?` and `.expect()` → `(<expr>)?`). The wrapping closure
already returns `Option<_>`, so `?` short-circuits. Add `rewrite_method_call`
arm for `method_name == "eval"` with zero args →
`Some(syn::parse_quote! { (#recv).try_eval()? })`. The codegen site in
`logic/mod.rs:2407` (HOL action lowering) already routes `rust_code` through
`safeify_methods_and_wrap`; the new arm makes every user `.eval()` Var-safe
automatically.

- **LoC**: ~10 in `rust_code_rewrite.rs`.
- **Risk**: LOW (additive; only changes user-visible behavior for terms that
  would have panicked).

### Layer 2: Viable-alt seeding filter

In `macros/src/gen/runtime/language.rs::prog_seed_match` (line ~2049-2068),
filter `all_alts()` by category-input-compatibility. For each alt, check
`alt.category() == input.dispatch_cat()` OR `alt.category()` is reachable via a
cast rule from `input.dispatch_cat()`. Use the existing `auto_inj_labels` set
(`parse_alt_filter.rs:102`) inverted: if `alt` is a pure auto-injected wrapper
around a different cat that's not in the input's compatibility set, skip
seeding. This is the **evidence-driven filter** the mandate demands —
categorically-incompatible alts are evidence-failed at the parse boundary.

- **LoC**: ~30 in `language.rs` (helper + filter in seed loop).
- **Risk**: MED (needs care to not break legitimate cross-cat seeds like
  `Int(NumLit(0))` seeded into `BigInt` via `IntToBigInt`).

### Layer 3: Keep multi-cat union extract as-is

With Layer 1 (no panics) and Layer 2 (fewer spurious seeds), the union extract
surfaces ALL cats' results without the regressions.

---

## Why Not Other Approaches

- **Per-alt isolated prog**: Each alt gets fresh `prog`, eval failures isolated.
  But N×ascent runtime (~5-10x slowdown for ambiguous `bitnot 0`), violates BCG05
  epoch sharing, and complicates equivalence-class merging. LoC ~80, RISK HIGH.
- **`catch_unwind` around eval**: Hides real bugs, requires `AssertUnwindSafe`,
  performance penalty, doesn't compose with Ascent's iter borrows. RISK HIGH.
- **First-alt-only with fallback**: Brittle heuristic ("empty" hard to define
  when partial results exist), violates P3 (disambiguation requires evidence).
- **Revert to single-cat extract**: Regresses `rhocalc_op` tests where
  `bitnot 0` needs cross-cat Int→BigInt result surfacing.

---

## Mandate Compliance

- **P1 (preserve all derivations)**: Layer 2's filter rules out by **evidence**
  (categorical incompatibility derivable from the grammar's cast lattice).
  Layer 1 makes evaluation Var-safe so non-rule-applicable alts gracefully
  yield `None`/`Err` — that's evidence-driven, not weight-driven.
- **P3 (disambiguation requires evidence)**: Eval failure under `try_eval()`
  returning `None` IS evidence (the term didn't reduce). Silently-dropping
  panics was weight-like (arbitrary unwinding order); `try_eval` short-circuit
  is structural.

---

## File:Line Changes Summary

1. **`macros/src/gen/native/rust_code_rewrite.rs:200-294`** (`rewrite_method_call`):
   Add `eval` zero-arg arm → `(#recv).try_eval()?`. ~10 LoC.
2. **`macros/src/gen/runtime/language.rs:2049-2068`** (`prog_seed_match`): Wrap
   alt iteration with `if alt_compat_with_dispatch_cat(alt, &dispatch_cat,
   language)` guard. ~30 LoC including helper.
3. **`macros/src/gen/runtime/language.rs:2371-2380`** (pre-stratum block): mirror
   the same filter on pre-stratum's `for __alt in term.0.all_alts()`. ~5 LoC.
4. **`macros/src/gen/runtime/language.rs:2630-2641`** (core_prog_seed_match):
   mirror filter. ~5 LoC.
5. **`languages/tests/edge_case_tests.rs`**: No changes required (regressions
   resolve via Layer 1+2).

**Total**: ~50 LoC, RISK LOW-MED. Achieves zero regressions in `edge_case_tests`
AND fixes `rhocalc_op` cross-cat tests AND respects preserve-all-derivations.

---

## Critical Files for Implementation

- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/native/rust_code_rewrite.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/runtime/language.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/term_ops/parse_alt_filter.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/native/eval.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/languages/src/calculator.rs`
