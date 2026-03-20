# Signed BigRat (arbitrary-precision rationals) — design options

## Context

MeTTaIL already supports **signed bigint** literals (`<digits>n`) backed by `num-bigint`, with a **Copy**-compatible runtime wrapper (`CanonicalBigInt`) where AST / `moniker` integration requires it.

**Signed big rationals** — **surface syntax decision** (this doc): rationals are introduced **without** an `r` suffix, via a **constructor term** (see [Surface syntax — decision](#surface-syntax--decision)). The lexer still contains a transitional `**r`** stub (`IntLit::BigRatStub`) from earlier exploration; it can stay until **fraction literal sugar** lands, or be removed once constructor-only workflows are stable.

The goal of this document is to compare **representation**, **syntax/grammar**, **libraries**, and **integration** options before implementing real rationals.

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

### Constructing rationals (primary syntax)

- **Form**: bigrats are **ratios of bigints**, expressed as a **constructor** (language-defined term), not a dedicated numeric literal suffix in the first shipping shape.
- **Examples** (illustrative):
  - `fraction(3, 4)` — constant numerator and denominator.
  - `fraction(x, y)` — `x` and `y` are **bigint** (or bigint-compatible) **expressions**, including large values from `…n` literals or variables.
  - `z = fraction(12, 13)` — binding the rational result.
- **Typing**: the language ties `fraction` to a `BigRat` (or native `Ratio<BigInt>`) category; **strict** rules apply (no implicit mix with `i32` / `BigInt` as a scalar without explicit rules), consistent with the rest of MeTTaIL numeric typing.
- **Planned sugar** (later): a **single lexer token** `<digits>r/<digits>r` — see [Surface syntax — decision](#surface-syntax--decision).

### Division (`/`)

- **Meaning**: **rational division** in ℚ (exact), not floating-point division.
- **Illustrative identity**: `fraction(10, 3)` is the single rational **10/3**, which **algebraically** equals `**fraction(3, 1) + fraction(1, 3)`** (mixed-number decomposition: quotient plus proper fractional part). This highlights that arithmetic stays **exact**—unlike `f64`, where rounding breaks such identities.
- **Implementation note**: the `/` **operator** still normally produces **one** rational value (10/3). The decomposition `3 + 1/3` is a separate **canonical display** or **derived** form if the language exposes it (e.g. `div_mod`-style terms), not necessarily the primary result type of `/`.

### Modulus (`%`)

- **Stakeholder idea** (optional per language): on bigrats, `**%` could always yield 0**, because **exact** rationals satisfy **(a / b) × b = a** with **no rounding remainder**—unlike floating-point.
- **Framework position**: `**%` (and all operators) are defined at the language level**; languages may adopt the stakeholder reading, Euclidean-style remainder, or omit `%` on `BigRat` entirely.
- **Contrast** (if a language adopts the stakeholder reading): that is **not** integer Euclidean remainder. Integer `%` encodes “leftover after truncated/floored division.”
- **Edge cases**: each language defines divisor **0** and scope of `%` on rationals.

### Negation — “two’s complement”

- **Requirement**: negation is specified in terms of **two’s complement**, not merely “flip sign on the numerator.”
- **Scope**: for **general rationals**, a canonical two’s complement bitstring is **not** mathematically standard; languages typically either (a) restrict two’s complement to **integer-embedded** rationals `**fraction(k, 1)`**, or (b) fix a **dyadic fixed-point** or **width** so every value has a defined bit pattern.
- **Interaction with bitwise ops**: `**&`, `|`, `^`, …`on`BigRat`are defined in each language’s definition** (same principle as`%`). A language may choose **no** bitwise ops, a **(0, 1)** binary-expansion story, or something else; negation for **arbitrary`** BigRat`often remains **sign on numerator** in the`Ratio` layer unless the language ties negation to a bit-level view.

### Bitwise operators (`&`, `|`, `^`, …) — reference semantics (language-defined)

- **Framework position**: **bitwise operators are not fixed globally** by MeTTaIL / `mettail-runtime`. Each **language** chooses whether to define `&`, `|`, `^`, etc. on `BigRat`, and with what **domains** and **rules** (terms, rewrites, native eval).
- **Stakeholder reference** (a language *may* adopt this): restrict bitwise interpretation to **positive rationals in (0, 1)** and define operations via **binary expansions** past the radix point.
- **Example** (stakeholder illustration): `**fraction(1, 3) & fraction(3, 4) == fraction(1, 4)`**, motivated by **1/3 = 0.010101…₂** and **3/4 = 0.11000…₂**, yielding **1/4 = 0.01₂** under chosen bit-indexing rules.
- **If a language adopts the (0, 1) story**: values **outside** that domain are **undefined** for those ops unless the language extends the spec.
- **Design challenges** (for languages that adopt binary-fraction bitwise semantics on **(0, 1)**):
  1. **Non-terminating expansions** (e.g. 1/3): need **periodic-bit algebra**, **truncated precision**, or **dyadic-only** subset — **specified in the language**, not by the core framework.
  2. **Alignment** between operands with different repeating periods.
  3. **Separation from exact ℚ**: keep the `**Ratio`** algebraic layer and any **bitwise** view **clearly documented** in the language (same type vs split types).

### Summary matrix


| Feature            | Intended behavior (high level)                             | Standard `num-rational` alone?                                                  |
| ------------------ | ---------------------------------------------------------- | ------------------------------------------------------------------------------- |
| `+`, `-`, `*`, `/` | Exact ℚ arithmetic                                         | Yes for `+ * /`; `-` yes; match negation spec                                   |
| `%`                | **Language-defined** (may match “always 0” reading or not) | **No** — not fixed by `num-rational` for this semantics                         |
| Unary `-`          | Two’s complement per language spec                         | **Maybe** — only if spec reduces to sign flip on `num`/`den`                    |
| `&`, `             | `,` ^`                                                     | **Language-defined**; optional stakeholder-style binary expansion on **(0, 1)** |


---

## Surface syntax — decision

### Phase 1 — **Constructor-style** (no `r` suffix)

Rationals are formed by a **language-defined constructor** (name illustrative: `fraction`), taking **two arguments** that evaluate to **big integers** (or whatever the language fixes as the parameter type).

**Examples:**


| Example                | Role                                                        |
| ---------------------- | ----------------------------------------------------------- |
| `fraction(3, 4)`       | Constants → rational **3/4**.                               |
| `fraction(x, y)`       | `x`, `y` are **bigint** (or language-fixed) expressions.    |
| `z = fraction(12, 13)` | Bind result to `z` (typed as `BigRat` / rational category). |


**Pros:**

- **No new numeric literal suffix** in the lexer for phase 1; reuse existing **bigint** literal and variable machinery for arguments.
- Semantics and **strict typing** live in **language rules** (terms / rewrites / native eval), matching MeTTaIL’s “define it in the language” style.
- **Denominator zero** and **reduction** are natural constructor-time checks.

**Cons:**

- More verbose than a dedicated literal; **sugar** deferred to phase 2.

**Implementation notes:**

- The **exact constructor name** is declared in each language’s `**types`** (or equivalent) section — not hard-coded by the framework.
- **Nested rationals as arguments are forbidden at the type level**: e.g. `fraction(fraction(a, b), c)` is ill-typed; both arguments must be **bigint** (or whatever the language fixes), not `BigRat`.
- The pattern is **binary constructor on two bigint-valued expressions**.

### Phase 2 — **Syntax sugar: single-token fraction literal** (lexer composite)

Add a **lexer composite** that recognizes **one token** of the form:

```text
<digits>r/<digits>r
or
<digits>r
```

- **Per-language `literals`**: whether **radix prefixes** (`0x`, `0b`, `0o`), `**_`**, etc. apply to **each** side of the composite is **defined in that language’s `literals` section** — not fixed globally by the framework.
- **Unary minus**: **not** part of the composite token; use `**-fraction(3, 4)`** (or equivalent) instead of `-3r/4r`.
- **Meaning**: desugar to the same rational as `**fraction(<left>, <right>)`** (using that language’s declared constructor name) after parsing both digit runs as bigints inside the composite rule.
- **Pros**: ergonomic, unambiguous **one** literal token; avoids relying on infix `/` between two separate `…r` atoms.
- **Cons**: lexer and `prattail` pipeline work (dedicated pattern, eval hook); must not clash with `r`-suffix stub behavior — likely **replace** stub paths once sugar is specified.

### Superseded options

- **Binary division on two `…r` atoms** (`1r / 3r`): **not** the primary path; phase 2 prefers **one** composite token `…r/…r` instead.
- **Lone `<digits>r` as k/1**: optional future sugar; **not** required for phase 1 constructor-only workflow.

---

## Where the value lives: `IntLit` vs separate type

### Option V1 — **Extend `IntLit`**

Rename or add a variant such as `Rational(Ratio<BigInt>)` and retire `BigRatStub`.

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

**Decision (see [Design decisions](#design-decisions-answered))**: introduce a separate **RationalLit** (or equivalent) for phase-2 composite rationals; **do not** rename `IntLit`. With **constructor-first** syntax, phase 1 needs no rational literal enum variant. **V2** in spirit; exact name is an implementation choice (`RationalLit` recommended).

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

**Recommendation**: default to `**num-rational` + `Ratio<BigInt>`** for a first real implementation, mirroring the `num-bigint` decision.

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
| **Rational `/` vs mixed form** | See [Project-specific operational semantics](#project-specific-operational-semantics-stakeholder-requirements): `/` yields one ℚ value; `fraction(3,1) + fraction(1,3)` is an algebraic identity / optional decomposition API.  |
| `**%` on BigRat**              | **Language-defined**: each language’s rules choose semantics (including whether a stakeholder-style “always 0” reading applies). The framework does not fix `%` for `BigRat`.                                                   |
| **Two’s complement & bitwise** | Not provided by `num-rational`. **Bitwise** (and negation bit semantics) are **language-defined**; see [Design decisions](#design-decisions-answered) and stakeholder reference for optional **(0, 1)** binary-expansion story. |


The stakeholder section gives **optional reference** semantics (e.g. **(0, 1)** binary expansion and `**fraction(1,3) & fraction(3,4) == fraction(1,4)`**); **bitwise is still language-defined** if adopted.

---

## Phased rollout (suggested)

1. **Design lock-in**: **constructor-first** surface syntax; **new `RationalLit`** (not a rename of `IntLit`) when phase-2 sugar exists; backend (`num-rational` default); **formal write-ups** for **two’s complement** and **bitwise-on-binary-expansion** where languages need them.
2. **Phase 1 — Constructor**:
  - Define `fraction` (or chosen name) as a **term** with two **bigint** arguments; eval to `Ratio<BigInt>` (or **CanonicalBigRat**).
  - **Stub `…r`**: leave as-is, remove, or gate — until phase 2, languages need **no** `r` literal for the chosen design.
3. **Core ℚ operations**: `+`, `*`, `/`, and negation at least to the level of “sign on numerator” **unless** step 1 mandates full two’s complement from day one.
4. **Language example**: extend Calculator (or a demo language) with `BigRat`, `**fraction(num, den)`** (or the name declared in that language’s `types`), and rational `Add`/`Mul`/`Div` rules; tests for identities like **fraction(10,3) = fraction(3,1) + fraction(1,3)**.
5. **Phase 2 — Lexer sugar**:
  - Implement **single-token** `<digits>r/<digits>r`; **digit/radix/`_` rules are per language** in each language’s `literals` section (see [Design decisions](#design-decisions-answered)).
  - Emit a **RationalLit**-style payload (do **not** rename `IntLit`); retire stub paths as appropriate.
  - Desugar to the language’s constructor (e.g. `fraction(left, right)`) or equivalent internal representation.
6. **Language-level operators** (likely **separate milestones**): `**%`**, **two’s complement negation** (if desired), and **bitwise** `& | ^` are **defined in each language’s definition** — not imposed by the framework. Languages that adopt binary-fraction bitwise semantics specify **domain**, **non-dyadic / repeating** behavior, and tests.
7. **Tests**: constructor eval, integration REPL-style tests, edge cases (zero den, reduction); **phase 2** adds lexer tests for the composite literal.

---

## Design decisions


| #   | Topic                                                       | Decision                                                                                                                                                                                                                                    |
| --- | ----------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 1   | Rename **IntLit** when phase-2 sugar exists?                | **No.** Introduce a separate **RationalLit** (or equivalent) for composite rational tokens; keep **IntLit** for integers.                                                                                                                   |
| 2   | Composite `<digits>r/<digits>r`: radix / `_` on both sides? | **Per language:** rules are defined in each language’s **literals** section (full parity with `n` where desired, or decimal-only, etc.).                                                                                                    |
| 3   | Unary minus on composite literal (`-3r/4r`)?                | **Not** in the composite regex; use `**-fraction(3, 4)`** (or the language’s constructor name).                                                                                                                                             |
| 4   | **BigRational** / **CanonicalBigRat** placement?            | **A**dd **CanonicalBigRat** in **mettail-runtime** next to **CanonicalBigInt**.                                                                                                                                                             |
| 7   | `%` always zero on `BigRat`?                                | **Language-defined**; the framework does not impose `%` semantics globally.                                                                                                                                                                 |
| 8   | Constructor name; nested `fraction(fraction(a,b), c)`?      | **Constructor name** is declared in each language’s **types** section. **Nested** `fraction` applications where an argument is itself a **BigRat** are **forbidden at the type level** (both arguments must be bigint-typed, not rational). |


### `CanonicalBigRat` — recommendation (Q4)

**Prefer a `CanonicalBigRat` newtype in `mettail-runtime`**, alongside `CanonicalBigInt`, when `BoundTerm` / generated code needs a **Copy** handle to a non-**Copy** rational (`Ratio<BigInt>`).

**Rationale:**

- Matches the **existing integration pattern** for bigints (leaked or interned immutable value + `NonNull` or similar + documented `Send`/`Sync`).
- Keeps `**num-rational` + `num-bigint`** in one place for downstream crates (`mettail-languages`, generated eval).
- A **trait-only** abstraction adds little until a **second** rational backend (e.g. `rug`) is required; introduce a trait **then** behind a thin adapter.

### Q5. Two’s complement (technical note)

**Two’s complement** names a **finite** bit encoding of integers: a fixed width w, values in a range [-2^{w-1}, 2^{w-1}-1], and negation as invert-plus-one on w bits.

**Fixed width**

- **Pros:** Unambiguous bit patterns; aligns with hardware and with **bitwise** stories that need a definite bit index.
- **Cons:** Values outside the range **wrap** or are **undefined** unless the language adds rules.

**Arbitrary width (“big” two’s complement)**

- Often means: use **as many bits as needed** so the integer fits (variable-length two’s complement). Still well-defined for **integers**, but **not** a single canonical w for “the” bitwise view.

**All rationals vs integers only**

- For `**fraction(p, q)`** with q > 1, there is **no** universally agreed “the two’s complement bits of this rational” without extra structure:
  - **Integer case** `fraction(k, 1)`: map k to a two’s complement bitstring (fixed or big width) — **natural**.
  - **General rational:** common approaches are (1) **don’t** define two’s complement on the full type; use **sign/magnitude** in the `Ratio` layer, or (2) fix **dyadic fixed-point** (denominator 2^k) so the value is an integer in disguise, or (3) define two’s complement only on a **subset** (e.g. integers-as-rationals).

**Practical guidance:** treat **two’s complement negation** as applying to **integer-embedded** rationals or to a **language-chosen fixed representation**; keep **general** `BigRat` negation as **exact ℚ** (sign on numerator after canonical reduction) unless the language specifies otherwise.

---

## Related documents

- [Signed BigInt library selection](./signed-bigint-library-selection.md) — bigint backend choice and ecosystem constraints.
- Code today: `prattail/src/int_lit.rs` (`BigRatStub`), `macros/src/gen/syntax/parser/prattail_bridge.rs` (`BigRat` native suffix mapping), `prattail/src/lexer.rs` (native type name heuristic for `BigRat`). **Planned surface syntax** is **constructor-first**; stub/sugar evolution is described in [Surface syntax — decision](#surface-syntax--decision).

