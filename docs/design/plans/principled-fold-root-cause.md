# Principled Fold Rule Codegen — Root Cause Analysis

**Date**: 2026-05-17
**Branch**: `feature/wfst-architecture`
**Status**: design ready for user review (NO code modifications until approved)
**Replaces**:
- `~/.claude/plans/phase-d-multi-cat-extract-redesign.md` (rejected: still uses string vocabulary)
- `~/.claude/plans/principled-fold-res-shape.md` (rejected: just moves the discriminator)

---

## 1. The True Root Cause

The recurring string-vocabulary anti-pattern in fold codegen is a symptom of
**responsibility misplacement**: the fold codegen mixes two orthogonal concerns
and uses rule-name dispatch to discriminate between them.

The two concerns:

**Concern A — "Compute the value"**: lift a user's `rust_code` block into an
Ascent relation that produces `Option<T>` (where `None` means the computation
couldn't produce a value).

**Concern B — "What happens when the computation can't produce a value"**:
silently elide via Ascent guard, OR surface failure as an explicit AST term
(e.g., `Int::CastErrInt`) so downstream congruence/match rules can detect
failure.

The current fold codegen does both in a single block, deciding which mode
to use by looking at the rule's LABEL NAME. Hence the strings:

```rust
if matches!(label_str, "IntBin" | "UIntBin" | "FloatBin" | "FixedBin"
                       | "BigintCast" | "BigratCast") { ... }
```

The `Lift`/`LiftPlain` autoref-trait at `runtime/src/lib.rs:167-251` ALREADY
makes the "T vs Option<T>" return-type difference invisible at the codegen
layer — both flow through `Lift(...).lift()` and emerge as `Option<T>`.
So the only residual job the string vocabulary does is: pick a specific
`Cat::Err` / `Cat::CastErrX` variant for failure surfacing.

But surfacing-failure-as-a-term is a SEPARATE concern that already has a
first-class mechanism in the grammar: **rewrite rules**. The grammar can
say "if this expression is stuck, rewrite it to `CastErrInt`". That belongs
in the rewrite layer, not the fold layer.

The fold codegen using rule-name dispatch to embed this rewrite is a
category error — it conflates COMPUTE with REWRITE.

---

## 2. Where the Anti-Pattern Lives (Five Sites)

| # | Site | What it does | Vocabulary |
|---|------|--------------|------------|
| 1 | `macros/src/logic/mod.rs:2676-2691` | Literal-folds-to-self loop for CastErrX variants | `["CastErrInt", "CastErrUInt32", "CastErrFloat", "CastErrFixed", "CastErrBigInt"]` |
| 2 | `macros/src/logic/mod.rs:2927-2977` | Legacy `match` branch in cross-cat fold | `"IntBin" \| "UIntBin" \| "FloatBin" \| "FixedBin" \| "BigintCast" \| "BigratCast"` |
| 3 | `macros/src/logic/mod.rs:3009-3013` | `res_is_option` discriminator | same as #2 |
| 4 | `macros/src/logic/mod.rs:3404-3421` | `fold_fold_through_err` exception for `*Proc`-suffixed rule labels | `"IntBinProc" \| ...` |
| 5 | `macros/src/gen/native/eval.rs:191-199` | `hol_numeric_cast_option` `(cat, label)` tuple match | 6 (category, label) tuples |
| 5+ | `macros/src/gen/native/eval.rs:167-234` | `is_bigrat_fraction_option`, `hol_int_fact_option`, `hol_bigrat_div_zero_guard` | additional rule labels |

All five sites encode the SAME piece of knowledge ("which rule's `None`
should surface as which `Cat::Err` variant"). All five are
calculator-grammar-specific.

The same-category fold path at `mod.rs:2725-2843` is already principled —
it discriminates only on `category_has_err` (a structural query), not on
rule labels. That path is the structural template the cross-cat fold path
should mirror.

---

## 3. Design Space (Survey)

### Option A — Always-Option uniformity via `Lift`

Drop the legacy 6-label match; emit only `safe.map(|v| Cat::Lit(v))`;
`bind_res = if let Some(res) = ...`. **Cost**: silently elides cast failures.
**Verdict**: incomplete — loses observable Err semantics.

### Option B — Centralized `ERR_VARIANT_LABELS` table

Move the string list into `common.rs`, add `cat_err_variant_for()`.
**Verdict** (already rejected by user): still strings.

### Option C — `#[err]` / `is_fail_variant` AST flag

Tag fail variants explicitly. **Verdict** (already rejected): just relocates
the discriminator.

### Option D — Return-type inference

Sniff `rust_code` for trailing `Some(...)` / `None` / `Option<_>` signature.
**Verdict**: brittle for nested expressions; requires type info we don't
have at proc-macro time for general cases.

### Option E — Trait-dispatched `LiftWithFallback<F>`

Runtime trait taking a "fallback constructor" closure. **Verdict**: pushes
complexity into runtime traits; still needs per-rule fallback-Cat at the
call site, so something has to bind that.

### Option F — Restructure fold codegen to match step codegen

Step codegen at `mod.rs:2411 vs 2425` already discriminates ONLY on
`category_has_err` — no rule names. **Verdict**: this IS the structural
template the cross-cat fold should mirror.

### Option G — Separate "elide-on-fail" from "surface-as-Err-term"

Always emit elide-on-fail fold rules; let grammar authors add explicit
rewrites for failure surfacing. **Verdict**: cleanest semantics; the grammar
already supports rewrite rules so no DSL extension needed.

### Option H — Two-relation split `fold_<cat>` / `fold_err_<cat>`

The fold relation never produces error terms; a parallel relation tracks
failure. **Verdict**: solves the codegen problem but requires distinguishing
which fail variant via some non-name mechanism (back to Option C territory).

### Option I — Default-fail-variant via structural relation

"Unique zero-arg constructor with no rust_code that is reachable as a
fold-fixpoint." **Verdict**: ambiguous when grammar has both `Err` AND
`CastErrInt` (calculator does); falls back to string-style regex matching.

---

## 4. Recommended Solution: Option F + Option G Composition

### Step 1 — Unify cross-cat fold (Option F)

Replace `mod.rs:2925-3018` (~95 LoC) with:

```rust
let rust_code = &rule.rust_code.as_ref().unwrap().code;
let safe = crate::gen::native::rust_code_rewrite::safeify_and_wrap(rust_code);
let res_expr = quote! { #safe.map(|__v| #category::#num_lit(__v)) };
let bind_res = quote! { if let Some(res) = #res_expr; };
```

Delete `res_is_option`, the legacy 6-label match, the `BigratCast`/`IntBin`/
`UIntBin`/`FloatBin`/`FixedBin`/`BigintCast` branches.

**Effect**: cross-cat folds either succeed (producing `Cat::Lit(v)`) or fall
through (term stays as `int(2.5, 32)` — a "stuck cast").

### Step 2 — Surface failure via rewrite rules (Option G)

The semantic of "failed cast becomes `CastErrInt`" moves from baked-in
codegen to user-authored rewrites in the grammar:

```text
// In calculator.rs rewrites {} block:
| ~ ![{ crate::numeric_dispatch::calc_try_int_bin(&a, w).is_none() }] |- (int_bin a w) ~> cast_error_int;
```

One rewrite per surfacing rule. Written ONCE in the grammar. The codegen
never asks "which Err variant" because the GRAMMAR ANSWERS that question
directly.

### Step 3 — Delete derived sites

- **`mod.rs:2676-2691`** (literal-folds-to-self for CastErrX): keep ONLY the
  `Err`-variant fixpoint at lines 2666-2674; the CastErrX-specific loop is
  dead because fold no longer auto-emits them.
- **`mod.rs:3404-3421`** (`fold_fold_through_err` exception): delete the
  `matches!(label_str, "IntBinProc"|...)` branch; `filter_err` becomes
  uniform.
- **`eval.rs:186-200`** (`hol_numeric_cast_option`): delete entirely.

### Step 4 — Structural detection in eval.rs (Option D-light, syntactic)

Replace `eval.rs:167-234`'s four helpers with ONE:

```rust
/// Returns true if the rust_code expression's outermost form is
/// structurally an `Option<_>` producer (call to a `try_*` function,
/// explicit `Some(...)`/`None`, or `match` whose arms are `Some`/`None`).
fn rust_code_returns_option(code: &syn::Expr) -> bool { ... }
```

Walk the `syn::Expr` AST — no string comparisons on rule labels, no
`(category, label)` tuples. The check operates on the USER'S CODE which
is the only legitimate authority on what the code returns.

For the eval-arm panic message, drop the special-case entirely. A cast
rule's `.eval()` calls `calc_try_int_bin(&a, w)` returning `Option<i32>`.
Wrap with `.expect("evaluation reached unreachable cast-error sentinel;
should have been normalized")`. ONE site, no vocabulary.

---

## 5. Why This Is Principled (Structural Argument)

The proposal isn't aesthetic — it's structurally honest about layer
responsibilities:

- The **fold codegen layer**'s job: lift a user-authored value computation
  into an Ascent relation. Outputs `Option<Cat>`. Done.
- The **rewrite layer**'s job: define what happens when a computation can't
  produce a value (failure-as-term, retry, ignore, etc.). Already
  first-class in the grammar via the `rewrites` block.
- The **eval layer**'s job: invoke user code at evaluation time. Asks ONE
  structural question of the user's code: does it return Option? The answer
  comes from the SYNTACTIC SHAPE of the user's code, not from the rule's
  identity.

Conflating these layers via rule-name dispatch was a category error. The
solution removes the conflation: fold stops doing rewrite's job; eval stops
doing the user-code-author's job. No new mechanism, no new AST flag, no new
attribute, no new trait, no new vocabulary table — just **removal of
misplaced responsibility**.

---

## 6. Trade-offs (Honest Accounting)

### Gained

- All five string-vocabulary sites collapse.
- Cross-cat fold matches the structurally-clean step-codegen pattern.
- Future grammars with their own cast/bin rules need ZERO codegen changes
  — they just write rewrite rules for failure surfacing.
- Codegen becomes ~170 LoC shorter and uniformly readable.
- `eval.rs` loses four helpers (~70 LoC) plus corresponding match arms.

### Lost

- One semantic shift: failed casts no longer produce `CastErrInt` *in a
  single fold step*; they require a separate rewrite to "see" the failure.
- For most calculator-style grammars this is invisible (the rewrite fires
  immediately in the next fixpoint iteration).
- For grammars that observe intermediate terms (debug traces, fixpoint
  counting), the trajectory has one extra step.
- Existing test cases that assert "after fold, term is `CastErrInt`" need
  either (a) the rewrite added to the grammar, or (b) the assertion updated
  to "after fold + one rewrite step".

---

## 7. LoC and Migration

| File | Change | LoC |
|------|--------|-----|
| `macros/src/logic/mod.rs:2676-2691` | Delete CastErrX literal-fixpoint loop | -15 |
| `macros/src/logic/mod.rs:2925-3018` | Replace dual-shape branching with uniform Option<Cat> | -85 |
| `macros/src/logic/mod.rs:3404-3421` | Delete `fold_fold_through_err` exception | -18 |
| `macros/src/gen/native/eval.rs:167-234` | Replace 4 helpers with 1 structural detector | -40 |
| `macros/src/gen/native/eval.rs:541-594` | Collapse 4 branches into 1 Option-detection arm | -30 |
| `languages/src/calculator.rs` | Add 6 failure-surfacing rewrites + 3 zero-divisor / fact / fraction rewrites | +15 |

**Net: ~-170 LoC of codegen complexity, +15 LoC of grammar rewrites,
ZERO new abstractions.**

### Migration path

1. Feature-flag the change with `LanguageDef::emit_legacy_cast_err_fold = true`
   for one release cycle.
2. Calculator (and any other in-tree grammar) adds the rewrite rules and
   flips the flag.
3. Subsequent release: remove the flag and dead code paths.

Existing user grammars that didn't define rewrite rules still work because
the auto-generated congruence machinery (already in `congruence/mod.rs`)
will still propagate `CastErrInt` terms through outer constructors — only
the fold-fired auto-emission goes away.

---

## 8. Critical Files for Implementation

- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/logic/mod.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/native/eval.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/native/rust_code_rewrite.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/runtime/src/lib.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/languages/src/calculator.rs`
