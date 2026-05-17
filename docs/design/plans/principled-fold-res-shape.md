# Principled Fold `res_expr` Shape — Structural Detector

**Date**: 2026-05-17
**Branch**: `feature/wfst-architecture`
**Origin**: replaces fragile string-match at `macros/src/logic/mod.rs:3009-3012`

---

## Problem

The Phase D Layer 1.5 commit (`498b3e5`) introduced:

```rust
let res_is_option = !matches!(
    label_str.as_str(),
    "IntBin" | "UIntBin" | "FloatBin" | "FixedBin"
        | "BigintCast" | "BigratCast"
);
```

This violates the project-wide mandate "prefer pattern matching over
string comparisons" AND is tightly coupled to calculator's specific
rule labels. Future grammars with their own cast/bin labels would
silently break.

## Core Insight

The legacy `IntBin`/`UIntBin`/`FloatBin`/`FixedBin`/`BigintCast`/`BigratCast`
arms differ from the default cross-cat arm in ONE semantic dimension only:
**where does `None` go?** Legacy maps to a specific category-typed err
variant (`Int::CastErrInt`, `UInt32::CastErrUInt32`, `BigRat::Err`, …);
default silently elides via the Ascent guard. The "shape difference"
(`Cat` vs `Option<Cat>`) is incidental — both can be uniformly expressed
as `Option<Cat>` where the legacy branch uses `.or(Some(Cat::ErrVariant))`
to bake the fallback into the Option.

## Solution: Unify on `Option<Cat>`, derive None-target from grammar AST

### 1. `macros/src/logic/common.rs` (+~45 LoC)

```rust
const ERR_VARIANT_LABELS: &[&str] = &[
    "Err", "CastErrInt", "CastErrUInt32",
    "CastErrFloat", "CastErrFixed", "CastErrBigInt",
];

pub fn cat_err_variant_for(
    language: &LanguageDef,
    category: &Ident,
) -> Option<Ident> {
    language.terms.iter()
        .find(|r| r.category == *category
              && fold_field_count(r) == 0
              && ERR_VARIANT_LABELS.iter().any(|name| r.label == name))
        .map(|r| r.label.clone())
}
```

### 2. `macros/src/logic/mod.rs:2925–3018` (replace ~95 LoC with ~35 LoC)

Delete the entire `if matches!(label_str, "IntBin"|...)` block AND
the `res_is_option` discriminator. Replace with:

```rust
let rust_code = &rule.rust_code.as_ref().unwrap().code;
let safe = crate::gen::native::rust_code_rewrite::safeify_and_wrap(rust_code);
let opt_expr = quote! { #safe.map(|__v| #category::#num_lit(__v)) };
let res_expr = match common::cat_err_variant_for(language, category) {
    Some(err) => quote! { #opt_expr.or(Some(#category::#err)) },
    None      => opt_expr,
};
let bind_res = quote! { if let Some(res) = #res_expr; };
```

`bind_res` is now uniform — no shape discriminator anywhere.

### 3. Parallel same-category fold arm (`mod.rs:2780–2794`)

The existing same-category arm has the same dual shape (`Cat` vs
`Option<Cat>`) decided by `div_bigrat_zero_to_err || category_has_err`.
Unify it through `cat_err_variant_for` so the entire codegen has a
single bind shape (~30 LoC simplification).

### 4. Literal-folds-to-self arm (`mod.rs:2676–2691`)

The hardcoded `for cast_err in ["CastErrInt", ...]` loop is the EXACT
same vocabulary leak. Reuse `ERR_VARIANT_LABELS` from common.rs
(-5 LoC duplication).

### 5. Future-proof tagging (optional, +20 LoC in `ast/src/grammar.rs`)

Add `pub is_err_variant: bool` to `GrammarRule` and a `#[err]`
attribute parsed in the grammar DSL. Then `cat_err_variant_for`
becomes purely AST-driven with no name list at all. Until then, the
structural-vocabulary table is the bridge.

## Why this is principled

- **No string comparisons** at the discrimination site — `bind_res`
  is unconditional pattern match.
- **Single source of truth** for err vocabulary: one table in
  `common.rs` (eventually one AST flag).
- **Works for any grammar**: a grammar with `CastErrDecimal` only
  needs to register its label.
- **Zero runtime cost**: identical generated code — `or(Some(...))`
  on `None` is a one-instruction branch.
- **No allocations**: pure Ident handling at codegen time.
- **Preserves semantics**: cast-err variants are still reachable,
  only routed through `Option<Cat>` rather than via a parallel `match`.

## LoC Estimate

Net delta: **-60 LoC** in `mod.rs`, **+45 LoC** in `common.rs` →
**-15 LoC overall** with a vastly cleaner codegen.

## Critical Files

- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/logic/mod.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/logic/common.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/native/rust_code_rewrite.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/ast/src/grammar.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/languages/src/calculator.rs`
