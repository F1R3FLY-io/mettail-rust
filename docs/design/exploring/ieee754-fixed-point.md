# Design: IEEE 754 suffixed literals, float restrictions, and fixed-point numbers

**Status:** Implemented in Calculator and RhoCalc (see below)  
**Date:** March 2025  
**Related:** [Float support in Ascent](../made/native-types/float-support-ascent.md), [String / float / bool methods](../made/native-types/string_float_bool_methods.md), `runtime/src/canonical_float.rs`, `runtime/src/canonical_fixed_point.rs`, `prattail/src/float_lit.rs`, `prattail/src/fixed_lit.rs`, `languages/src/calculator.rs`, `languages/src/rhocalc.rs`

### Implemented behavior (summary)

- **Float literals:** `mettail_prattail::parse_float_lit` accepts unsuffixed, `f32`, or `f64` (reject `f128` / `f256`); `f32` is widened to `f64` for `CanonicalFloat64`. **Calculator and RhoCalc** only include optional `f64` in their float **lexer** pattern (no `f32` token in surface syntax, since neither language exposes `f32` as a type).
- **Fixed-point:** `mettail_runtime::CanonicalFixedPoint` (`unscaled` / `places`, value `unscaled / 10^places`). Literals use `…p…` forms parsed by `parse_fixed_lit`. Lexer uses `fixed_by_category` parallel to rationals. Calculator has `Fixed` terms and `ProcFixed`; RhoCalc uses `CastFixed` on `Proc` with `+` / `-` / `*` / `/` / `%` and `bitand` / `bitor` / `bitxor` on fixed values only.
- **Float restrictions:** No `%` or bitwise operators on `Float` in these languages (only on `Fixed` / integers as before).

---

## 1. Context: how numbers work in this repo today

### 1.1 Concrete languages and the `language!` macro

Operations are **not** defined by a single global semantics DSL. Each language (`Calculator`, `RhoCalc`, …) declares:

- **Types** with native Rust payloads, e.g. `![i32] as Int`, `![f64] as Float`, `![mettail_runtime::CanonicalBigInt] as BigInt`.
- **Literals** with a lexer regex and an `eval` block (often calling `mettail_prattail`).
- **Terms** with HOL blocks `![{ … }]` implementing reduction for literals (and `fold` / `step` as needed).

Integer-style arithmetic in **RhoCalc** is folded on `Proc` by dispatching on `CastInt`, `CastBigInt`, `CastBigRat`, `CastFloat`, etc. (see `Add`, `Sub`, `Mul`, `Div` in `languages/src/rhocalc.rs`). **Calculator** uses separate term rules per type (`AddInt`, `AddFloat`, …).

Any new numeric kind should follow the same pattern: **define parsing + operations inside each language** that should expose it.

### 1.2 Float as implemented

- Ascent / term enums require `Eq + Hash`. Raw `f32`/`f64` are wrapped as **`CanonicalFloat32` / `CanonicalFloat64`** (`runtime/src/canonical_float.rs`): canonical NaN, `-0` → `+0`, total `Ord`, `BoundTerm`.
- The `language!` macro maps `![f32]` → `CanonicalFloat32` and `![f64]` → `CanonicalFloat64` (`macros/src/gen/types/enums.rs`).
- **Literals** today: a single regex in `calculator.rs` / `rhocalc.rs` that matches decimal / exponent forms **without** a `f32`/`f64` suffix; `eval` strips `_` and uses `parse::<f64>()` only — so everything is effectively **double precision** in the surface syntax even when the category is `Float` backed by `CanonicalFloat64`.
- `CanonicalFloat64` currently implements **`Rem`** (Rust `%`). The desired language semantics say **floating-point must not** use modulus (or bitwise operators) at all; see §3.

### 1.3 What does not exist yet

- Suffixed IEEE literals (`-1.234e5f32`, `f64`, and optionally `f128` / `f256`).
- A **fixed-point** numeric type: syntax `<digits>p<digits>`, division/modulo semantics, bitwise semantics.
- **RhoCalc** has no `%` on `Proc` for integers in the same style as `+` (Calculator has `ModInt` for `Int` only).

---

## 2. IEEE 754 floating-point literals and types

### 2.1 Surface syntax (C99-style + width suffix)

Target grammar (after `_` removal inside digit runs, consistent with existing int/float literals):

- General shape: optional sign, fractional / exponent form, then **mandatory or optional suffix** depending on language policy.
- Examples: `-1.234e5f32 == -123400f32`, `1.0f64`, hex floats are **out of scope** unless explicitly added later.

**Width policy (recommended for the first iteration):**

| Suffix | Meaning | Rust storage |
|--------|---------|--------------|
| `f32` | IEEE binary32 | `CanonicalFloat32` |
| `f64` | IEEE binary64 | `CanonicalFloat64` |
| `f128` / `f256` | Reserved / future | Either **reject in parser** with a clear error, or map to a software type (e.g. `f128` crate) behind a feature — not required for MVP. |

**Unsuffixed float literals:** Two compatible options:

1. **Language-defined default:** e.g. require `f32` or `f64` always (strict C99-like).
2. **Default to `f64`:** extend the current regex with an optional `(f32|f64)?`; absent suffix → `f64` (backward compatible for existing tests and snippets).

Recommendation: **(2)** for Calculator/RhoCalc: optional suffix, default to what defined in the `literals` section.

### 2.2 Lexer / parser work

- **New or extended helper** in `mettail_prattail` (alongside `parse_int_lit`, `parse_rational_lit`): e.g. `parse_float_lit(text) -> Result<(CanonicalFloat32 | CanonicalFloat64), ()>` or return an enum `FloatLit { F32(...), F64(...) }`.
- **Regex split:** Either one literal kind with a capturing suffix, or **two** literal entries `Float32` / `Float64` with ordered patterns (same as `UInt32` before `Int` today) so `1.0f32` is not swallowed by a greedy `f64` arm.
- **Scientific notation:** Parse significand and exponent, apply width-specific range/rounding (Rust `f32::from_str` / `f64::from_str` already match IEEE parsing for decimal strings).

### 2.3 Language definitions

- **Option A — single category `Float`:** Keep `![f64] as Float` only; widen literals to parse suffix and **coerce** `f32` literals to `f64` (loses distinct `f32` semantics). **Not recommended** if `f32` is a requirement.
- **Option B — two categories (recommended):** `![f32] as Float32`, `![f64] as Float64` (names illustrative), each with literals that only accept the matching suffix (or default `f64` for `Float64` and `f32` for `Float32` if you want strictness).
- **Option C — one AST category, two variants:** One Rust enum `FloatWidth { F32(CanonicalFloat32), F64(CanonicalFloat64) }` as the native type in `language!` — only if the macro pipeline can be extended cleanly; today the idiomatic path is separate categories or a single canonical width.

**Calculator / RhoCalc:** Mirror the pattern used for integers (multiple concrete types vs one `Proc` dispatch). RhoCalc would add `CastFloat32` / `CastFloat64` or generalize `CastFloat` once widths exist.

### 2.4 “SIMD-like” numeric type (optional note)

If later you want a vector float without full SIMD in the theory: introduce a **separate** category (e.g. `Float32xN` wrapping `[CanonicalFloat32; N]` or a small newtype) in **one** language first; keep IEEE scalars separate. This document does not specify SIMD layout.

---

## 3. Operations that must **not** exist on floats (early errors)

**Requirement:** Modulus (`%`) and bitwise operators (`&`, `|`, `^`, `~`, `<<`, `>>`, and any language-spelled equivalents) are **undefined** on floating-point; errors should happen **as early as possible**.

### 3.1 Parse time

- **Do not** add grammar rules `Float % Float`, `Float & Float`, etc.
- If the lexer encodes `%` as a single token, overload resolution will simply fail if no rule matches — **good**.

### 3.2 Type-directed checks (optional hardening)

If the grammar shares tokens with integers (e.g. `%` only on `Int` today), ambiguous mixes like “future generic `%`” could appear when types are inferred. Mitigations:

- Keep **separate** term constructors per type (as Calculator does for `ModInt`).
- Add a **validation pass** in `macros` or a small static check over generated grammars listing forbidden `(operator, category)` pairs for float categories — only if the architecture ever introduces a generic binop.

### 3.3 Runtime / HOL

- **Remove or stop using** `Rem` on `CanonicalFloat32` / `CanonicalFloat64` in **language** reduction code paths if any surface syntax could reach it (today languages should not expose `%` on Float; the trait impl can remain for internal tests or be documented as “not part of surface semantics”).
- Do not implement float bitwise in HOL blocks.

---

## 4. Fixed-point numbers

### 4.1 Syntax

After stripping `_` from digit runs:

1. **Integral mantissa:** `<digits> p <digits>` — e.g. `10p1` (the second digit run is the **scale** / number of fractional decimal places).
2. **Leading digits + point:** `<digits> . <optional digits> p <digits>` — e.g. `3.14p2`.
3. **No leading digits:** `. <digits> p <digits>` — e.g. `.5p1` for `0.5` at one decimal place.

**Scale:** Non-negative integer `p` in the grammar; interpret as **decimal** places (base-10 fixed point), consistent with the examples below.

**Radix:** Decimal only for MVP (no `0x…p3` unless specified later).

**Lexer ordering:** Fixed-point patterns must be **more specific** than integer literals where needed (e.g. `10p1` must not be parsed as `10` + identifier `p1`). A regex that requires **digit + `p` + digit** for this form avoids collision with identifiers starting with `p`.

### 4.2 Semantic model

Represent a value as a pair **(unscaled, places)** with `unscaled: BigInt`, `places: u32`:

\[
\text{value} = \frac{\text{unscaled}}{10^{\text{places}}}
\]

**Construction from literal:**

- `10p1` → unscaled `100`, places `1` → value `10.0`.
- `3.3p1` → unscaled `33`, places `1` → `3.3`.
- `.5p1` → unscaled `5`, places `1` → `0.5`.

This matches “bigint with shifted decimal point.”

### 4.3 Runtime type

Introduce something like:

```rust
// Illustrative — actual name/location: mettail_runtime, e.g. canonical_fixed_point.rs
pub struct CanonicalFixedPoint {
    unscaled: CanonicalBigInt, // or BigInt inside a Copy handle, same patterns as BigRat
    places: u32,
}
```

Requirements:

- **`Eq`, `Hash`, `Ord`, `BoundTerm`** (same reasons as `CanonicalBigRat` / floats in Ascent).
- **Normalization policy:** Decide whether `(10, 1)` and `(100, 2)` are the same value — recommend **canonical form**: divide `unscaled` and `places` by common powers of ten until trailing zeros in the decimal expansion are removed, with a rule for **zero** (`0p0` or `0pk` for any `k`).

### 4.4 Arithmetic (same `places` — binary ops)

For binary `+`, `-`, `*`, `/`, `%`:

1. **Align places** to `P = max(places_a, places_b)` by scaling unscaled values:  
   `ua' = ua * 10^(P - pa)`, `ub' = ub * 10^(P - pb)`.

2. **Add / sub:** `unscaled = ua' ± ub'`, `places = P`; then normalize.

3. **Mul:** `unscaled = ua * ub`, `places = pa + pb`; normalize.

4. **Div (shifted integer division),** matching the user example `10p1 / 3p1 == 3.3p1`:

   After alignment to common `P`,  
   \[
   \text{unscaled\_quot} = \frac{u_a' \cdot 10^P}{u_b'}
   \]
   using **integer** division on `BigInt`, and result places = `P`.  
   Check: `a=100, b=30, P=1` → `100 * 10 / 30 = 33` → `3.3p1`. ✓

5. **Mod (C99 identity):**  
   \[
   (a / b) \times b + (a \bmod b) = a
   \]
   at the shared precision model. With `q` the quotient from (4),  
   \[
   r_{\text{unscaled}} = u_a' - \frac{q \cdot u_b'}{10^P}
   \]
   (integer arithmetic arranged so the result is exact in fixed point at place `P`).  
   Example: `10p1 % 3p1` → `0.1p1`. ✓

Document **division by zero** as `Proc::Err` / language error, consistent with `Div` on `BigRat` / integers in RhoCalc.

**Mixed-scale examples** should be added as unit tests in `languages/tests/` once implemented.

### 4.5 Bitwise operators on fixed-point

The spec says: *“Bitwise operators should satisfy x op y = bigrat(x) op bigrat(y).”*

**Issue:** `CanonicalBigRat` has no bitwise operations; bitwise is naturally defined on **integers**.

**Recommended semantics (implementable, matches “exact rational then integer bit view”):**

1. Map each fixed-point value to its **exact** rational (trivially `unscaled / 10^places`).
2. Choose a common scale `S = max(places_x, places_y)` (same as arithmetic alignment).
3. Map to **integers** `ix = unscaled_x * 10^(S - places_x)`, `iy = …`.
4. Define `x op y` (for `&`, `|`, `^`, …; shifts may need a single **right-hand** integer operand) as the fixed-point value obtained from `(ix op iy)` with places `S`, then normalize.

This is **equivalent** to “do bitwise on the unscaled numerators after aligning decimal points,” which is the usual fixed-point reading. If product stakeholders insist on a different reading of `bigrat(x)`, capture that as an amendment; the above is the default engineering interpretation.

**Unary `~`:** Apply to aligned integer or to `ix` at scale `S` for the single operand.

### 4.6 Comparison and mixed-type rules

- **Equality:** After normalization, compare `(unscaled, places)` or compare as `CanonicalBigRat`.
- **Cross-type with `BigRat` / `Float`:** Out of scope for MVP; recommend **disallow** implicit mixing (force explicit conversion functions in the language), or define a small table per language (e.g. fixed → `BigRat` exact, `Float` may round).

### 4.7 `language!` integration

1. New type: `![mettail_runtime::CanonicalFixedPoint] as Fixed` (name TBD).
2. New literal block with regex + `parse_fixed_lit` in `prattail`.
3. In **Calculator**: term rules `AddFixed`, `DivFixed`, … mirroring `AddInt` / `AddBigRat`.
4. In **RhoCalc**: extend `Add` / `Sub` / `Mul` / `Div` / future `Mod` dispatch with `CastFixed` arms, same style as `CastBigRat`.
5. **Congruence / rewrite rules:** Generated from terms; add congruence rules for each new constructor (pattern matches existing `AddIntCongL` style in `calculator.rs`).

---

## 5. Implementation plan (ordered)

1. **Prattail:** `parse_float_lit` with optional/default suffix; tests in `prattail/src/tests/`.
2. **Prattail:** `parse_fixed_lit` + normalization; property tests for round-trip of decimal strings.
3. **Runtime:** `CanonicalFixedPoint` with `Eq`/`Hash`/`Ord`/`BoundTerm` and arithmetic helpers (div/mod as specified).
4. **Macros:** No change expected if using existing `![Type] as Name` paths; confirm literal payload generation for the new type (mirror `BigRat`).
5. **Languages:** Update `Float` literal regex + eval; add `Float32` category or split literals as decided in §2.3.
6. **Languages:** Add `Fixed` to Calculator and RhoCalc with operations defined in HOL blocks.
7. **Tests:** `languages/tests/calculator.rs`, `rhocalc_tests.rs`: float suffixes, fixed div/mod identity, fixed bitwise vs aligned-bigint reference.
8. **Docs:** Update manual / EBNF dump (`prattail/docs/usage/ebnf-dump.md`) when grammar tokens stabilize.

---

## 6. Open questions

1. **Unsuffixed float:** Confirm default `f64` vs require explicit suffix everywhere.
2. **f128/f256:** Reject at parse time vs feature-gated software implementation.
3. **Fixed vs `BigInt` literal collision:** e.g. is `10p1` ever ambiguous with a hypothetical `p` suffix on integers? (Current codebase has no `p` suffix for ints — low risk.)
4. **Bitwise spec:** Confirm with theory owners that “align scales then integer bitwise” matches the intent of `bigrat(x) op bigrat(y)`.
5. **RhoCalc `%` on integers:** If parity with C99 fixed-point mod identity is desired for `Int`, that is separate from this doc but may be added alongside `Mod` on `Proc` for `CastFixed`.

---

## 7. Summary

| Feature | Today | Target |
|--------|--------|--------|
| Float literals | Unsuffixed, `f64` parse only | Optional `f32`/`f64` suffixes; typed widths |
| Float `%` / bitwise | Not in grammar; `Rem` exists on canonical type | Forbid in grammar and HOL; optional trait cleanup |
| Fixed point | Absent | `…p…` syntax, `CanonicalFixedPoint`, div/mod as specified, bitwise via aligned unscaled integers |
| Where semantics live | Per-language `language!` terms | Same: implement in Calculator, RhoCalc, and any other front-end that needs these types |

This keeps the same architecture as integers and rationals: **concrete languages own the operation tables**; runtime provides canonical, Ascent-friendly value types; prattail provides parsing.
