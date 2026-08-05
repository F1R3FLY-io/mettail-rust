# Design: IEEE 754 suffixed literals, float restrictions, and fixed-point numbers

**Status:** Implemented in Calculator and Rholang (see below)  
**Date:** March 2025  
**Related:** [Float support in Ascent](../made/native-types/float-support-ascent.md), [String / float / bool methods](../made/native-types/string_float_bool_methods.md), `runtime/src/canonical_float.rs`, `runtime/src/canonical_fixed_point.rs`, `prattail/src/float_lit.rs`, `prattail/src/fixed_lit.rs`, `languages/src/calculator.rs`, `languages/src/rholang.rs`

### Implemented behavior (summary)

- **Float literals:** `mettail_prattail::parse_float_lit` accepts unsuffixed, `f32`, or `f64` (reject `f128` / `f256`); `f32` is widened to `f64` for `CanonicalFloat64`. **Calculator and Rholang** only include optional `f64` in their float **lexer** pattern (no `f32` token in surface syntax, since neither language exposes `f32` as a type).
- **Fixed-point:** `mettail_runtime::CanonicalFixedPoint` preserves the structural pair
  `(unscaled, places)`; scale is part of identity, including for zero. Binary arithmetic,
  ordered comparisons, and binary bitwise operators require equal scales, matching upstream
  Rholang. Multiplication preserves that scale and floor-truncates the product back onto its
  decimal grid. Literals use `…p…` forms parsed by `parse_fixed_lit`.
- **Float restrictions:** No `%` or bitwise operators on `Float` in these languages (only on `Fixed` / integers as before).

---

## 1. Context: how numbers work in this repo today

### 1.1 Concrete languages and the `language!` macro

Operations are **not** defined by a single global semantics DSL. Each language (`Calculator`, `Rholang`, …) declares:

- **Types** with native Rust payloads, e.g. `![i32] as Int`, `![f64] as Float`, `![mettail_runtime::CanonicalBigInt] as BigInt`.
- **Literals** with a lexer regex and an `eval` block (often calling `mettail_prattail`).
- **Terms** with HOL blocks `![{ … }]` implementing reduction for literals (and `fold` / `step` as needed).

Integer-style arithmetic in **Rholang** is folded on `Proc` by dispatching on `CastInt`, `CastBigInt`, `CastBigRat`, `CastFloat`, etc. (see `Add`, `Sub`, `Mul`, `Div` in `languages/src/rholang.rs`). **Calculator** uses separate term rules per type (`AddInt`, `AddFloat`, …).

Any new numeric kind should follow the same pattern: **define parsing + operations inside each language** that should expose it.

### 1.2 Float as implemented

- Ascent / term enums require `Eq + Hash`. Raw `f32`/`f64` are wrapped as **`CanonicalFloat32` / `CanonicalFloat64`** (`runtime/src/canonical_float.rs`): canonical NaN, `-0` → `+0`, total `Ord`, `BoundTerm`.
- The `language!` macro maps `![f32]` → `CanonicalFloat32` and `![f64]` → `CanonicalFloat64` (`macros/src/gen/types/enums.rs`).
- **Literals:** Calculator and Rholang accept unsuffixed binary64 literals and the explicit `f64`
  suffix. The shared parser can also parse `f32`, but neither language exposes a binary32 carrier.
- `CanonicalFloat64` currently implements **`Rem`** (Rust `%`). The desired language semantics say **floating-point must not** use modulus (or bitwise operators) at all; see §3.

### 1.3 Deliberately unsupported surfaces

- Calculator and Rholang do not expose `f32`, `f128`, or `f256` carriers.
- Float remainder and float bitwise operators remain unavailable.
- Fixed-point binary operators do not infer or align scales. Call `fixed(value, places)` explicitly
  when a scale migration is intended.

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

Recommendation: **(2)** for Calculator/Rholang: optional suffix, default to what defined in the `literals` section.

### 2.2 Lexer / parser work

- **New or extended helper** in `mettail_prattail` (alongside `parse_int_lit`, `parse_rational_lit`): e.g. `parse_float_lit(text) -> Result<(CanonicalFloat32 | CanonicalFloat64), ()>` or return an enum `FloatLit { F32(...), F64(...) }`.
- **Regex split:** Either one literal kind with a capturing suffix, or **two** literal entries `Float32` / `Float64` with ordered patterns (same as `UInt32` before `Int` today) so `1.0f32` is not swallowed by a greedy `f64` arm.
- **Scientific notation:** Parse significand and exponent, apply width-specific range/rounding (Rust `f32::from_str` / `f64::from_str` already match IEEE parsing for decimal strings).

### 2.3 Language definitions

- **Option A — single category `Float`:** Keep `![f64] as Float` only; widen literals to parse suffix and **coerce** `f32` literals to `f64` (loses distinct `f32` semantics). **Not recommended** if `f32` is a requirement.
- **Option B — two categories (recommended):** `![f32] as Float32`, `![f64] as Float64` (names illustrative), each with literals that only accept the matching suffix (or default `f64` for `Float64` and `f32` for `Float32` if you want strictness).
- **Option C — one AST category, two variants:** One Rust enum `FloatWidth { F32(CanonicalFloat32), F64(CanonicalFloat64) }` as the native type in `language!` — only if the macro pipeline can be extended cleanly; today the idiomatic path is separate categories or a single canonical width.

**Calculator / Rholang:** Mirror the pattern used for integers (multiple concrete types vs one `Proc` dispatch). Rholang would add `CastFloat32` / `CastFloat64` or generalize `CastFloat` once widths exist.

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

```math
\text{value} = \frac{\text{unscaled}}{10^{\text{places}}}
```

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

Requirements, now implemented:

- **`Eq`, `Hash`, `Ord`, `BoundTerm`** key on the exact `(unscaled, places)` pair.
- **No implicit normalization:** `(10, 1)` and `(100, 2)` are distinct fixed-point values even
  though they denote the same rational number. Zero likewise preserves its declared scale, so
  `0p0`, `0.0p1`, and `0.00p2` remain structurally distinct.

### 4.4 Arithmetic (equal declared scales only)

Every binary fixed-point arithmetic operation first requires `places_a == places_b == P`.
Mismatched scales are refused; the evaluator yields the language error term. An explicit
`fixed(value, P)` cast is the only scale migration.

1. **Add / sub:** `unscaled = ua ± ub`, `places = P`.

2. **Mul:** `unscaled = floor(ua * ub / 10^P)`, `places = P`. Floor division, rather than
   truncation toward zero, is significant for negative products and matches upstream Rholang.

3. **Div (shifted integer division):**

   ```math
   \text{unscaled\_quot} = \frac{u_a \cdot 10^P}{u_b}
   ```

   using `BigInt` integer division, with result scale `P`. For example,
   `10.0p1 / 3.0p1 == 3.3p1`.

4. **Mod — remainder on the unscaled integers, scale preserved:**

   ```math
   r_{\text{unscaled}} = u_a \bmod u_b, \qquad \text{places} = P
   ```

   using `BigInt`'s `%`, which truncates toward zero so the sign follows the **dividend** (as
   Rust's `i64 %` and C99's `%` both do).
   Example: `10.0p1 % 3.0p1` → `100 mod 30 = 10` → `1.0p1`. ✓

   This is upstream Rholang's definition verbatim — `combine_mod`'s `GFixedPoint` arm,
   `f1r3node-rust-mettail/rholang/src/rust/interpreter/reduce.rs:3460-3470`.

   The exact remainder always fits the type because `u_a mod u_b` is no wider than `u_a`.
   Division must approximate; remainder does not.

   The retired implementation instead returned the division truncation residual
   `a - trunc_P(a/b) * b`. That was not a remainder and disagreed with upstream; regression tests
   retain `7.50p2 % 2.00p2 == 1.50p2` so the residual formula cannot reappear.

Division or remainder by zero yields the language error term. Scale mismatch is checked first, so
a mixed-scale operation whose right operand is zero is classified as a scale refusal, matching the
upstream dispatch order.

### 4.5 Bitwise operators on fixed-point

Binary `bitand`, `bitor`, and `bitxor` require equal scales and apply the operation directly to the
two unscaled integers, preserving that scale. Mixed scales are refused because decimal rescaling is
not a bit shift and upstream supplies no contrary fixed-point bitwise rule.

Unary `bitnot` applies `!` to the unscaled integer and preserves the operand's declared scale.

### 4.6 Comparison and mixed-type rules

- **Equality / hashing:** structural on `(unscaled, places)`.
- **Ordering:** the total Rust `Ord` compares represented numeric value first and then uses scale as
  a deterministic tie-break. The four language ordered relations (`<`, `<=`, `>`, `>=`) first
  require equal scales, then compare the unscaled integers; they never expose that scale tie-break
  to source programs.
- **Cross-type operations:** require an explicit cast or a declared lossless promotion.

### 4.7 `language!` integration

The integration is complete: both languages declare `CanonicalFixedPoint` as `Fixed`, share the
literal parser, expose the operator rules described above, and generate their ordinary congruence
and evaluation machinery from those declarations.

---

## 5. Verification surfaces

- `runtime/src/canonical_fixed_point.rs` pins raw-pair identity and each checked operation.
- `runtime/src/safe_arith.rs` pins scale-mismatch reasons and multiplication flooring.
- `languages/tests/fixedpoint_scale_dedup_{ab,rholang}.rs` pin structural scale identity, explicit
  rescaling, and mixed-scale refusal.
- `languages/tests/rholang_arith_carrier_matrix.rs` pins the Rholang carrier matrix.
- `rholang-runtime/tests/rho_rholang_conformance.rs` compares the generated fold with the reducer.

---

## 6. Open questions

1. **f128/f256:** remain reserved until a software carrier and explicit language surface are chosen.
2. **Binary32 language surface:** the shared parser understands `f32`, but Calculator and Rholang do
   not yet expose a `CanonicalFloat32` category.

---

## 7. Summary

| Feature | Current behavior | Status |
|--------|--------|--------|
| Float literals | Unsuffixed or `f64` in Calculator/Rholang | Implemented |
| Float `%` / bitwise | Not in either language's grammar | Implemented refusal by absence |
| Fixed point | Structural scale; same-scale binary ops; explicit rescaling | Implemented and gated |
| Where semantics live | Per-language `language!` terms plus checked runtime helpers | Implemented |

This keeps the same architecture as integers and rationals: **concrete languages own the operation tables**; runtime provides canonical, Ascent-friendly value types; prattail provides parsing.
