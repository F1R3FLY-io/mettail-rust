# Signed BigRat (arbitrary-precision rationals) — design options

**As implemented today:** `num-rational`’s `Ratio<BigInt>` behind a **`Copy`** handle **`CanonicalBigRat`** (`runtime/src/canonical_bigrat.rs`); rational **literals** `…r` and `…r/…r` via **`RationalLit`** and `parse_rational_lit` (`prattail/src/rational_lit.rs`, `TokenKind::RationalLit`); per-language **`BigRat`** literal patterns in `languages/src/calculator.rs` and `languages/src/rhocalc.rs`. **Constructor** `fraction`: on **Calculator** it builds `BigRat` from two **BigInt** terms; on **RhoCalc** it is **`FractionProc`** with two **Proc** arguments (typically `CastBigInt`), evaluated with **`fold`** so Ascent emits `fold_proc` / `rw_proc` (see `languages/src/rhocalc.rs`).

The remainder of this document records **target semantics**, **library options**, and **still-language-defined** behavior (`%`, bitwise, two’s complement on general rationals). It mixes historical decisions with the current codebase.

## Context

MeTTaIL supports **signed bigint** literals (`<digits>n`) backed by `num-bigint`, with a **Copy**-compatible runtime wrapper (`CanonicalBigInt`) where AST / `moniker` integration requires it (see [signed-bigint-library-selection.md](./signed-bigint-library-selection.md)).

**Signed big rationals** use both **constructor** forms and **`r`-suffix literals** in shipping languages; see [Surface syntax — decision](#surface-syntax--decision).

---

## Requirements (target semantics)

1. **Signed arbitrary-precision rationals** (exact fractions), not floating-point approximations.
2. **Canonical representation** (e.g. reduced form: gcd of numerator and denominator is 1; denominator positive) — either enforced at construction or lazily on demand (policy choice).
3. **Strict typing** consistent with the rest of the integer work: `BigRat` must not implicitly mix with `i32`, `BigInt`, etc., unless the language defines explicit coercions or operators (including for `fraction(...)` arguments and results).
4. **Parser/lexer coherence** for the intended surface syntax (see below).
5. **Runtime integration** compatible with generated AST and binding/substitution (`BoundTerm`): expect the same class of constraints as `BigInt` (likely a **Copy** handle or codegen that uses `.clone()` consistently — see [signed-bigint discussion](./signed-bigint-library-selection.md) and runtime wrappers).

Non-goals for an initial slice (unless explicitly requested):

- Decimal reals, continued fractions, or algebraic numbers.
- Interval arithmetic.

---

## Project-specific operational semantics

The following constraints go beyond “plain `Ratio<BigInt>` in ℚ” and should drive language rules, tests, and any dedicated `BigRat` runtime layer.

### Constructing rationals (constructor + literals)

- **Constructor**: language-defined `fraction` (name fixed per language). **Calculator:** `fraction(a, b)` with `a`, `b` : **BigInt**. **RhoCalc:** `fraction(a, b)` with `a`, `b` : **Proc** (semantic code expects `CastBigInt` / literals `…n`).
- **Literals**: patterns such as `<digits>r` and `<digits>r/<digits>r` with per-language regex + `parse_rational_lit`; values stored as **`CanonicalBigRat`** in the **BigRat** category.
- **Typing**: languages keep rationals in **`BigRat`** / **`CastBigRat`** (RhoCalc) and define explicit casts and homogeneous `+ - * /` on those forms; no implicit mix with fixed-width ints without rules.

### Division (`/`)

- **Meaning**: **rational division** in ℚ (exact), not floating-point division.
- **Illustrative identity**: `fraction(10, 3)` is the single rational **10/3**, which **algebraically** equals `fraction(3, 1) + fraction(1, 3)` (mixed-number decomposition: quotient plus proper fractional part). This highlights that arithmetic stays **exact**—unlike `f64`, where rounding breaks such identities.
- **Implementation note**: the `/` **operator** still normally produces **one** rational value (10/3). The decomposition `3 + 1/3` is a separate **canonical display** or **derived** form if the language exposes it (e.g. `div_mod`-style terms), not necessarily the primary result type of `/`.

### Modulus (`%`)

- **Stakeholder idea** (optional per language): on bigrats, `%` could always yield **0**, because **exact** rationals satisfy **(a / b) × b = a** with **no rounding remainder**—unlike floating-point.
- **Framework position**: `%` (and all operators) are defined at the **language** level; languages may adopt the stakeholder reading, Euclidean-style remainder, or omit `%` on `BigRat` entirely.
- **Contrast** (if a language adopts the stakeholder reading): that is **not** integer Euclidean remainder. Integer `%` encodes “leftover after truncated/floored division.”
- **Edge cases**: each language defines divisor **0** and scope of `%` on rationals.

### Negation — “two’s complement”

- **Requirement**: negation is specified in terms of **two’s complement**, not merely “flip sign on the numerator.”
- **Scope**: for **general rationals**, a canonical two’s complement bitstring is **not** mathematically standard; languages typically either (a) restrict two’s complement to **integer-embedded** rationals `fraction(k, 1)`, or (b) fix a **dyadic fixed-point** or **width** so every value has a defined bit pattern.
- **Interaction with bitwise ops**: `&`, `|`, `^`, … on `BigRat` are defined in each **language** (same principle as `%`). A language may choose **no** bitwise ops, a **(0, 1)** binary-expansion story, or something else; negation for **arbitrary** `BigRat` often remains **sign on numerator** in the `Ratio` layer unless the language ties negation to a bit-level view.

### Bitwise operators (`&`, `|`, `^`, …) — reference semantics (language-defined)

- **Framework position**: **bitwise operators are not fixed globally** by MeTTaIL / `mettail-runtime`. Each **language** chooses whether to define `&`, `|`, `^`, etc. on `BigRat`, and with what **domains** and **rules** (terms, rewrites, native eval).
- **Stakeholder reference** (a language *may* adopt this): restrict bitwise interpretation to **positive rationals in (0, 1)** and define operations via **binary expansions** past the radix point.
- **Example** (stakeholder illustration): `fraction(1, 3) & fraction(3, 4) == fraction(1, 4)`, motivated by **1/3 = 0.010101…₂** and **3/4 = 0.11000…₂**, yielding **1/4 = 0.01₂** under chosen bit-indexing rules.
- **If a language adopts the (0, 1) story**: values **outside** that domain are **undefined** for those ops unless the language extends the spec.
- **Design challenges** (for languages that adopt binary-fraction bitwise semantics on **(0, 1)**):
  1. **Non-terminating expansions** (e.g. 1/3): need **periodic-bit algebra**, **truncated precision**, or **dyadic-only** subset — **specified in the language**, not by the core framework.
  2. **Alignment** between operands with different repeating periods.
  3. **Separation from exact ℚ**: keep the `Ratio` algebraic layer and any **bitwise** view **clearly documented** in the language (same type vs split types).

### Summary matrix


| Feature            | Intended behavior (high level)                             | Standard `num-rational` alone?                                                  |
| ------------------ | ---------------------------------------------------------- | ------------------------------------------------------------------------------- |
| `+`, `-`, `*`, `/` | Exact ℚ arithmetic                                         | Yes for `+ * /`; `-` yes; match negation spec                                   |
| `%`                | **Language-defined** (may match “always 0” reading or not) | **No** — not fixed by `num-rational` for this semantics                         |
| Unary `-`          | Two’s complement per language spec                         | **Maybe** — only if spec reduces to sign flip on `num`/`den`                    |
| Bitwise ops (`&`, `\|`, `^`, …) | **Language-defined**; optional stakeholder-style binary expansion on **(0, 1)** | **No** — not fixed by `num-rational` for arbitrary bitwise semantics |


---

## Surface syntax — decision

### Phase 1 — **Constructor-style**

Rationals are formed by a **language-defined constructor** (e.g. **`fraction`**), taking two arguments typed per language (**BigInt** in Calculator; **Proc** with `CastBigInt` operands in RhoCalc).

**Examples:**


| Example                | Role                                                        |
| ---------------------- | ----------------------------------------------------------- |
| `fraction(3, 4)`       | Constants → rational **3/4**.                               |
| `fraction(x, y)`       | `x`, `y` are **bigint** (or language-fixed) expressions.    |
| `z = fraction(12, 13)` | Bind result to `z` (typed as `BigRat` / rational category). |


**Pros:**

- Reuses **bigint** literal and variable machinery for arguments where the constructor takes bigints.
- Semantics and **strict typing** live in **language rules** (terms / rewrites / native eval).
- **Denominator zero** and **reduction** are constructor- or eval-time checks (`try_from_nd`, `Proc::Err`, etc.).

**Cons:**

- More verbose than a dedicated literal when literals are not used.

**Implementation notes:**

- The constructor is declared in each language’s **`terms`** section (and types for categories), not hard-coded by the framework.
- **Nested rationals as arguments** are ill-typed where arguments must be **BigInt** / `CastBigInt` (Calculator / RhoCalc).

### Phase 2 — **`r`-suffix rational literals** (implemented)

PraTTaIL recognizes **one token** per literal, of the form:

```text
<digits>r/<digits>r
or
<digits>r
```

- **Per-language `literals`**: radix prefixes (`0x`, `0b`, `0o`), digit separators `_`, etc. are **defined in that language’s `literals` section** (see `parse_rational_lit` tests in `prattail/src/rational_lit.rs`).
- **Unary minus**: **not** part of the rational literal token; use negation on the **Proc** / **BigRat** expression (e.g. unary `-` where the language defines it).
- **Meaning**: parsed to **`RationalLit`** → **`CanonicalBigRat`** in the **BigRat** category (not desugared at parse time to `fraction` in the current pipeline).
- **Infix** `1r / 3r` is still available in languages that define **`/`** on **`BigRat`** / **`CastBigRat`** (exact division); it is complementary to the single-token literal form.

### Literal vs constructor

- **Single-token** `…r` / `…r/…r` and **constructor** `fraction(…)` coexist; authors may prefer literals for constants and `fraction` when building from **bigint** expressions.

---

## Where the value lives: `IntLit` vs separate type

### Option V1 — **Extend `IntLit`**

Rename or add a variant such as `Rational(Ratio<BigInt>)` inside `IntLit` (not chosen).

- **Pros**: one pipeline for “numeric literal atoms” in prattail.
- **Cons**: name `IntLit` becomes a misnomer; rational is not an integer; more variant churn in every `match`.

### Option V2 — **New `RationalLit` (or `NumericLit`) enum**

Split integer and rational literal payloads; lexer emits distinct token kinds or tagged values.

- **Pros**: clear semantics; avoids bloating integer-only matches.
- **Cons**: more plumbing in lexer/codegen/bridge tests.

### Option V3 — **Keep stub in `IntLit`, map at trampoline**

Keep stub for token typing only; convert to a real `BigRat` AST payload only when building the native literal arm.

- **Pros**: minimal change to `IntLit` during transition.
- **Cons**: two-stage story is easy to get wrong; long-term debt.

**Decision (implemented):** separate **`RationalLit`** struct and **`TokenKind::RationalLit`** in PraTTaIL; **`IntLit`** remains integer-only. Implemented name: **`RationalLit`** in `prattail/src/rational_lit.rs`.

---

## Library / backend options

Assumption: stay aligned with the existing **bigint** choice (`num-bigint`) unless there is a strong reason to fork stacks.

### 1) `num-rational` with `Ratio<num_bigint::BigInt>`

The `num-rational` crate provides `Ratio<T>` for integer types implementing `Integer` + friends. With `num-bigint`, this yields a standard **pure-Rust** rational type (often exposed as `BigRational` when using the crate’s `num-bigint` feature).

- **Pros**: same ecosystem family as current `BigInt`; well-understood semantics; reduced fractions via `Ratio` API.
- **Cons**: another dependency; need to wire features consistently across workspace crates.

### 2) `rug` (`Rational`)

- **Pros**: very fast; same stack as GMP-backed integers.
- **Cons**: native library/toolchain burden (same reasons `rug` was deprioritized for bigint in this project).

### 3) `fraction` (and similar “fraction” crates)

- **Pros**: ergonomic rational-centric APIs in some cases.
- **Cons**: second parallel numeric stack; integration and long-term alignment with `num-bigint` choice may be weaker than `num-rational`.

### 4) **Custom `struct BigRat { num: BigInt, den: BigInt }`**

- **Pros**: zero new deps; full control invariants.
- **Cons**: reinvent gcd, reduction, parsing, `Display`, `Hash` stability — high bug surface.

**Recommendation (implemented):** **`num-rational`** + **`Ratio<BigInt>`**, wrapped as **`CanonicalBigRat`** for **`Copy`** / **`BoundTerm`** compatibility, mirroring **`CanonicalBigInt`**.

---

## Runtime / AST integration (BoundTerm, `Copy`)

`num_bigint::BigInt` and typical rational types are **Clone** but not **Copy**.

Expect the same pattern as `CanonicalBigInt`:

- either a **CanonicalBigRat** (**Copy** handle to interned or leaked `Ratio<BigInt>`), **or**
- systematic codegen fixes so **no** derived macro assumes `Copy` on rational payloads.

Document the chosen invariant (immutability after construction, thread-safety story) next to `CanonicalBigInt`.

---

## Semantics & edge cases


| Topic                          | Decision to record in implementation                                                                                                                                                                                            |
| ------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Zero denominator**           | Parse error vs runtime panic vs `None` — pick one and test it (Parse error preferred).                                                                                                                                          |
| **Sign canonicalization**      | e.g. negative sign on denominator normalized away.                                                                                                                                                                              |
| **Reduction**                  | Always reduce on construction vs lazy — affects `Eq`/`Hash` and performance.                                                                                                                                                    |
| **Equality**                   | `Ratio` structural equality after canonicalization.                                                                                                                                                                             |
| **Mixed ops**                  | `BigRat + BigInt` forbidden by default unless language adds rules (consistent with strict int typing).                                                                                                                          |
| **Display / debug**            | Stable string form for REPL and tests.                                                                                                                                                                                          |
| **Rational `/` vs mixed form** | See [Project-specific operational semantics](#project-specific-operational-semantics): `/` yields one ℚ value; `fraction(3,1) + fraction(1,3)` is an algebraic identity / optional decomposition API.  |
| `%` on `BigRat`              | **Language-defined**: each language’s rules choose semantics (including whether a stakeholder-style “always 0” reading applies). The framework does not fix `%` for `BigRat`.                                                   |
| **Two’s complement & bitwise** | Not provided by `num-rational`. **Bitwise** (and negation bit semantics) are **language-defined**; see [Design decisions](#design-decisions-answered) and stakeholder reference for optional **(0, 1)** binary-expansion story. |


The stakeholder section gives **optional reference** semantics (e.g. **(0, 1)** binary expansion and `fraction(1,3) & fraction(3,4) == fraction(1,4)`); **bitwise is still language-defined** if adopted.

---

## Phased rollout (status)

1. **Done — backend:** `num-rational` + **`CanonicalBigRat`** in `mettail-runtime`; reduction via `Ratio::new` at construction.
2. **Done — literals:** **`RationalLit`** / **`parse_rational_lit`** in PraTTaIL; per-language **`BigRat`** literal blocks; **`TokenKind::RationalLit`** in the lexer.
3. **Done — constructors:** **Calculator** `fraction` on **BigInt**; **RhoCalc** **`FractionProc`** on **Proc** with **`fold`** (not `step`) so non-native **Proc** gets **`fold_proc`** rules.
4. **Done — core ℚ on languages:** Calculator and RhoCalc define rational **`+ - * /`**, comparisons, and casts as needed; tests in `languages/tests/`.
5. **Open / per language:** `%`, bitwise, and strict **two’s complement** stories on full **`BigRat`** (see stakeholder sections above); formal write-ups only where a language adopts them.
6. **Tests ongoing:** constructor eval, `…r` lexer tests (`prattail/src/rational_lit.rs`), integration tests (`languages/tests/calculator.rs`, `languages/tests/rhocalc_tests.rs`).

---

## Design decisions


| #   | Topic                                                       | Decision                                                                                                                                                                                                                                    |
| --- | ----------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 1   | Rename **IntLit** when phase-2 sugar exists?                | **No.** Introduce a separate **RationalLit** (or equivalent) for composite rational tokens; keep **IntLit** for integers.                                                                                                                   |
| 2   | Composite `<digits>r/<digits>r`: radix / `_` on both sides? | **Per language:** rules are defined in each language’s **literals** section (full parity with `n` where desired, or decimal-only, etc.).                                                                                                    |
| 3   | Unary minus on rational literal (`-3r/4r`)?                | **Not** part of the literal token; use unary `-` on the expression (or `-fraction(3, 4)` where the language provides it).                                                                                                                                             |
| 4   | **BigRational** / **CanonicalBigRat** placement?            | **`CanonicalBigRat`** in **mettail-runtime** next to **`CanonicalBigInt`** (**implemented**).                                                                                                                                                             |
| 7   | `%` always zero on `BigRat`?                                | **Language-defined**; the framework does not impose `%` semantics globally.                                                                                                                                                                 |
| 8   | Constructor name; nested `fraction(fraction(a,b), c)`?      | Constructor is declared in each language’s **`terms`** (and categories in **`types`**). **Nested** `fraction` where an argument is **BigRat** / wrong type is **ill-typed** in Calculator / RhoCalc (bigint / `CastBigInt` arguments only). |


### `CanonicalBigRat` — recommendation (Q4)

**Prefer a `CanonicalBigRat` newtype in `mettail-runtime`**, alongside `CanonicalBigInt`, when `BoundTerm` / generated code needs a **Copy** handle to a non-**Copy** rational (`Ratio<BigInt>`).

**Rationale:**

- Matches the **existing integration pattern** for bigints (leaked or interned immutable value + `NonNull` or similar + documented `Send`/`Sync`).
- Keeps `num-rational` + `num-bigint` in one place for downstream crates (`mettail-languages`, generated eval).
- A **trait-only** abstraction adds little until a **second** rational backend (e.g. `rug`) is required; introduce a trait **then** behind a thin adapter.

### Q5. Two’s complement (technical note)

**Two’s complement** names a **finite** bit encoding of integers: a fixed width w, values in a range [-2^{w-1}, 2^{w-1}-1], and negation as invert-plus-one on w bits.

**Fixed width**

- **Pros:** Unambiguous bit patterns; aligns with hardware and with **bitwise** stories that need a definite bit index.
- **Cons:** Values outside the range **wrap** or are **undefined** unless the language adds rules.

**Arbitrary width (“big” two’s complement)**

- Often means: use **as many bits as needed** so the integer fits (variable-length two’s complement). Still well-defined for **integers**, but **not** a single canonical w for “the” bitwise view.

**All rationals vs integers only**

- For `fraction(p, q)` with q > 1, there is **no** universally agreed “the two’s complement bits of this rational” without extra structure:
  - **Integer case** `fraction(k, 1)`: map k to a two’s complement bitstring (fixed or big width) — **natural**.
  - **General rational:** common approaches are (1) **don’t** define two’s complement on the full type; use **sign/magnitude** in the `Ratio` layer, or (2) fix **dyadic fixed-point** (denominator 2^k) so the value is an integer in disguise, or (3) define two’s complement only on a **subset** (e.g. integers-as-rationals).

**Practical guidance:** treat **two’s complement negation** as applying to **integer-embedded** rationals or to a **language-chosen fixed representation**; keep **general** `BigRat` negation as **exact ℚ** (sign on numerator after canonical reduction) unless the language specifies otherwise.

---

## Related documents

- [Signed BigInt library selection](./signed-bigint-library-selection.md) — bigint backend choice and ecosystem constraints.
- Code: `prattail/src/rational_lit.rs` (**`RationalLit`**), `prattail/src/int_lit.rs` (integers only), `runtime/src/canonical_bigrat.rs`, `macros/src/gen/syntax/parser/prattail_bridge.rs` (native category / literal eval wiring), `languages/src/calculator.rs`, `languages/src/rhocalc.rs` (**`FractionProc`**, **`fold`**).

