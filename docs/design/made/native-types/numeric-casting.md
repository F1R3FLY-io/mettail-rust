# Numeric casting — design

**Status:** Implemented in `mettail-runtime` + Calculator + RhoCalc (details below).  
**Related:** [IEEE 754 / fixed-point exploration](../exploring/ieee754-fixed-point.md), [Signed BigRat](./signed-bigrat-design.md), [Float support in Ascent](./float-support-ascent.md), `language!` native types (`languages/src/*.rs`), shared cast dispatch (`runtime/src/numeric_cast_dispatch.rs`, `languages/numeric_dispatch.rs`)

### Implementation status (codebase)

- **Runtime (`mettail-runtime`):** `numeric_cast` (`runtime/src/numeric_cast.rs`) — width validation (`int`/`uint`: `m = 2^n`, `n ≥ 3`; `float`: **32 and 64** only; **80 / 128 / 256** → `CastError::UnsupportedFloatWidth`), `fixed` place count with a documented cap, floor/modular/interval rules, and unit tests. Language-agnostic cast pipelines (**no `Proc`**) live in **`numeric_cast_dispatch`** (`runtime/src/numeric_cast_dispatch.rs`): they take `NumericInput` and width parameters only; language layers should delegate here rather than duplicating conversion logic.
- **Languages crate glue:** Per-language **`Proc` → `NumericInput`** (list peeling, tag mapping) and thin wrappers around the runtime pipelines are in **`languages/numeric_dispatch.rs`** (next to `languages/src/`, not under it, so `src/` stays for `language!` definitions). Calculator and RhoCalc builtins import from `crate::numeric_dispatch`.
- **Calculator:** Binary **`int`**, **`uint`**, **`float`**, **`fixed`** (second argument is width / place count), unary **`bigint`**, **`bigrat`**. There is **no** unary `int(proc)` or `float(proc)`; use **`int(p, m)`** / **`float(p, m)`** (and `Proc` projections **`bool`**, **`str`** where needed). Invalid casts reduce to per-category nullary errors (`cast_error_int`, …) where applicable.
- **RhoCalc:** Same builtins at **`Proc`** level (`int(arg, w)`, … inside `{ … }` blocks). Failures map to **`Proc::Err`** (display **`error`**). Ascent fold rules for these casts allow a final **`Proc::Err`** (unlike most `Proc` folds that suppress `Err` until subterms are ready).
- **Float storage:** `float(arg, 32)` rounds to **binary32** then uses the language float carrier (`CanonicalFloat64` / `f64`); tie-breaking and overflow (`±Inf`) follow the runtime helpers and tests.
- **Large integer widths:** Targets that do not fit existing `Int` / `UInt32` / `BigInt` carriers follow language-specific rejection; very wide `m` may require `BigInt` in the surface.
- **Surface literals:** `…n` (`BigInt`) tokens **may** use a leading `-` (e.g. **`-1n`**). You can still use **`Int`** −1 in **`uint(-1, 8)`**, **`bitnot 0`**, etc.; semantics for signed sources follow §4.

## 1. Summary

Conversion between numeric types is **explicit**. The language exposes **builtins** (`int`, `uint`, `bigint`, `bigrat`, `float`, `fixed`) rather than implicit widening/narrowing coercions. This document specifies their semantics, overflow and rounding rules, interactions with **mixed runtime** expressions in an otherwise **untyped** surface language, and **alternatives** considered for coercion policy.

---

## 2. Builtin cast forms

All width or precision parameters named `m` below are **signed 64-bit integers** at the language level (same class as other integer parameters); implementations validate ranges before applying semantics.

**Concrete syntax (implemented):** Calculator and RhoCalc use **`int(arg, m)`**, **`uint(arg, m)`**, **`float(arg, m)`**, and **`fixed(arg, m)`** for width-bearing casts (RhoCalc: inside **`{ … }`** expression blocks). Unary **`bigint`** and **`bigrat`** match the names below. The subsections use the same names for semantics.

### 2.1 `int(arg, m)`

- **Result:** signed **m-bit** integer (`i8` … `i64` / extended widths as the runtime defines).
- **When `m = 2^n` for integer `n ≥ 3`:** `arg` is converted with **rounding toward −∞** (floor on the real line). Example: `int(-3.5f32, 8) == -4` as `i8`.
- **Otherwise:** **error** (invalid width).
- **From larger fixed-width integers to smaller:** **modular** reduction in two’s complement representation (see §4).
- **From signed to unsigned via `uint`:** not applicable here; see §4 for cross-kind integer rules.

### 2.2 `uint(arg, m)`

- **Result:** **unsigned** m-bit integer (`u8` … — note: the width parameter selects the bit width of the **unsigned** type).
- **When `m = 2^n` for `n ≥ 3`:** same floor-style rounding toward −∞ for non-integers; **negative** values **clamp to 0** before or as part of mapping into the unsigned range. Example: `uint(3.5f32, 8) == 3u8`, `uint(-3.5f32, 8) == 0u8`.
- **Otherwise:** **error**.

### 2.3 `bigint(arg)`

- **Result:** signed arbitrary-precision integer (`…n` / `BigInt`).
- **Rounding:** toward **−∞** (floor). Example: `bigint(-3.5f32) == -4n`.

### 2.4 `bigrat(arg)`

- **Result:** signed arbitrary-precision rational (`BigRat`).
- **From integers, rationals, fixed-point (exact representations):** **exact** conversion.
- **From floating-point:** use the **least** real value in the **interval** denoted by the floating-point value (consistent with IEEE rounding toward −∞ when that interval is half-open from below). This ties float→rational semantics to the float’s **value interval**, not to “parse the decimal string.”

### 2.5 `float(arg, m)`

- **Result:** IEEE 754 binary floating-point of width **m** bits.
- **When `m ∈ {32, 64, 80, 128, 256}`:** convert to the **nearest** representable value of that format (ties and NaN payload rules should follow a single documented IEEE mode; **±Inf** allowed when magnitude overflows finite range).
- **Otherwise:** **error**.

### 2.6 `fixed(arg, m)`

- **Result:** fixed-point number with **`m` decimal places** after the point (`CanonicalFixedPoint`-style: value = unscaled / 10^m_places in spirit; here **`m` is the place count**).
- **Rounding:** toward **−∞** (floor in the real value, then express in fixed-point). Examples: `fixed(3.49p2, 1) == 3.4p1`, `fixed(-3.49p2, 1) == -3.5p1` (using the language’s concrete `p` syntax for fixed literals).
- **From floating-point:** take the **least** value in the interval denoted by the float (same principle as `bigrat` from float), then apply floor into the fixed-point grid.

---

## 3. Error conditions (overflow and non-finite values)

| Situation | Behavior |
|-----------|----------|
| Cast **Inf** or **NaN** to any **non-float** numeric type | **Overflow / domain error** (not silent undefined behavior). |
| Cast from a **non-integer** real type to an **integer** type | Error if **⌊value⌋** (floor) is **not representable** in the target integer type’s **mathematical** range (after any float interval lower bound is taken for float sources). |
| **Widen** float to smaller float where exponent range is insufficient | May yield **±Inf** (e.g. `float(1e50f64, 32)` may be `+Inf` in `f32`). |
| Invalid `m` for `int` / `uint` / `float` | **Error** at cast site. |

---

## 4. Integer narrowing, widening, and signed ↔ unsigned

- **Larger integer → smaller integer (same signedness family):** **modular** arithmetic in the target width. Example: `uint(257u16, 8) == 1u8`.
- **Signed integer → unsigned integer of width `m`:** preserve **two’s complement bit pattern** modulo `2^m`. Example: value **−1** maps to **255** in 8 bits (e.g. **`uint(-1, 8)`** in Calculator, **`{uint(bitnot 0, 8)}`** in RhoCalc). **`BigInt`** −1 behaves the same; literals may be **`-1n`**.
- **Unsigned → signed:** language must specify whether high bit set is **preserved as negative** (standard two’s complement reinterpretation) or **rejected**; the table in §3 assumes **reinterpretation** unless a given language adds stricter checks.

These rules apply **after** any floor/clamp steps defined for `int`/`uint` from non-integers (e.g. `uint` clamps negatives to 0 **before** modular reduction into the unsigned width).

---

## 5. Alternatives (language design)

### 5.1 Directed acyclic graph of implicit coercions

**Idea:** Smaller numeric types implicitly widen toward a common type in expressions (C/C++/Java/Scheme-style).

**Trade-offs:** Fewer explicit calls at call sites; risk of surprising precision loss or performance (unexpected `f64` in hot paths). **This design rejects implicit widening** for numeric casts in favor of §2.

### 5.2 Multiple dispatch (Julia-style)

**Idea:** No central coercion table; each **binary** operator is defined on **each pair** of numeric types, with conversions written explicitly in those definitions. Could be expressed with **patterns** in a functional sublanguage and could scale to **user-defined numeric types**.

**Compatibility:** Orthogonal to §2. A language may still expose `int(...)`, `float(...)`, etc., as **primitive** conversions while using multiple dispatch for `+`, `*`, `/` at pairs of types.

---

## 6. Runtime conversions: untyped operands and mixed operations

**Problem:** In an **untyped** or unityped process calculus, a value like `x` in `x / 30u64` has no static type. How should the implementation choose evaluation order and **common type**?

**Options:**

1. **Greatest lower bound / “bigger” type (dynamic languages):** When one operand carries a **concrete** numeric tag (`u64` literal, `f64`, etc.) and the other is **unknown** until runtime, promote the unknown to a **compatible supertype** (e.g. rational + integer → rational; integer + float → float) using the same **explicit** rules as builtins where possible.
2. **Strict:** Require **explicit** `float(x, 64)` / `uint(x, 64)` before mixing with a suffixed literal — maximally predictable, noisier at call sites.
3. **Channel / process typing:** For `for (@x <- chan) { y!(x / 4) }`, treat `x` as **value-dynamic**; define `/` only on pairs where runtime tags are known, or define a **default** (e.g. all unknowns as `BigRat` or as `f64`) — this is a **per-language** policy, not fixed by the MeTTaIL framework.

**Recommendation for documentation:** Separate **(a)** **static** explicit casts (§2) from **(b)** **runtime dispatch** rules in each language’s reduction semantics. Default promotion should be **documented per language** (Calculator vs RhoCalc already differ in how `Proc`-level arithmetic is folded).

---

## 7. Literal syntax vs type-qualified literals

Two notations often appear in discussion:

- **Suffix style:** `10.23f64` (C/Java-like; already familiar in [IEEE literal design](../exploring/ieee754-fixed-point.md)).
- **Quasi-quotation / type-first:** `` f64`10.23` `` (type name followed by a literal body).

**Design note:** Both can denote the same **IEEE** value if parsing is unified. Choose one **primary** surface form per language for consistency; the other can be sugar desugaring to the same AST node. Backtick forms avoid ambiguity with identifiers ending in `f64` and scale to **user-defined** numeric types more uniformly.

---

## 8. Implementation checklist (MeTTaIL codebase)

When implementing or extending:

1. **Parser / lexer:** width-bearing casts as **`int`**, **`uint`**, **`float`**, **`fixed`** (plus unary **`bigint`**, **`bigrat`**) consistent with `language!` term naming; **no** unary `int`/`float` on `Proc`.
2. **Runtime:** map `m` to `i8`…`i512` or arbitrary widths per §2; `float` widths to `CanonicalFloat32` / `CanonicalFloat64` / future extended floats; `fixed` to `CanonicalFixedPoint`. Reuse **`numeric_cast_dispatch`** for shared cast behavior; add **`languages/numeric_dispatch.rs`** glue (`Proc` → `NumericInput`) when wiring a new language that exposes the same builtins.
3. **Errors:** surface **overflow** and **invalid `m`** as **catchable** language errors (or reduction failures), not panics in user code paths.
4. **Tests:** matrix over source types × targets × edge cases (NaN, Inf, −0, two’s complement, modular narrow).

---

## 9. Open questions

- Should **`uint(..., m)`** from **negative bigint** always clamp to **0**, or error for “negative to unsigned” except when the source is **already** an unsigned modular bit pattern? (Current proposal: **clamp** for real negatives; **two’s complement** when the operation is defined as reinterpreting signed bits — clarify in language spec if both paths exist.)
- **Tie-breaking** for `float` **nearest** mode: IEEE default **ties to even** unless the language pins **toward +∞ / −∞ / toward zero**.
- **`f80` / `f128` / `f256`:** storage strategy (hardware vs soft float) per [float exploration](../exploring/ieee754-fixed-point.md).
