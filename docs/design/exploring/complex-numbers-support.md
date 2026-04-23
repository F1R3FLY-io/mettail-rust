# Complex Number Support for Calculator and RhoCalc

**Status:** Accepted (v1 decisions recorded)  
**Scope:** Add first-class complex numbers to both `calculator` and `rhocalc` language definitions, following existing native-type integration patterns (`Float`, `BigRat`, `Fixed`).

## Goals

- Add a native complex type that can be parsed, displayed, hashed, compared for equality, and used in Ascent relations.
- Integrate complex numbers into both languages:
  - `calculator`: typed category operations (`Complex` category and `Proc` injection).
  - `rhocalc`: `Proc`-centric operations via `CastComplex`.
- Keep behavior deterministic and consistent with current error patterns (`Err`/`error` term where applicable).
- Minimize surface-area changes and avoid unrelated refactors.

## Non-Goals (Initial Version)

- No symbolic complex algebra (e.g., simplification rules over variables).
- No branch-heavy complex analysis functions initially (`log`, `arg`, multi-valued roots).
- No implicit numeric promotion across unrelated categories unless explicitly specified.
- No changes to existing public APIs beyond adding a new category/type and associated operations.

## Current Architecture Notes

- `calculator` has per-category terms (`Int`, `Float`, `BigRat`, `Fixed`, ...) and `Proc` injections (`ProcInt`, `ProcFloat`, ...).
- `rhocalc` is mostly `Proc`-driven with explicit `Cast*` wrappers and type-checked fold semantics.
- Runtime already provides canonical wrappers for Ascent-safe native numeric types:
  - `CanonicalFloat64`
  - `CanonicalBigInt`
  - `CanonicalBigRat`
  - `CanonicalFixedPoint`
- Numeric cast pipelines are centralized in `runtime` (`numeric_cast.rs`, `numeric_cast_dispatch.rs`) and adapted per language in `languages/numeric_dispatch.rs`.

Complex support should follow this pattern rather than introducing ad-hoc semantics inside language files.

## Library Evaluation and Recommendation

Given the near-term roadmap includes advanced complex arithmetic/functions, we should adopt a dedicated complex math library now and keep MeTTaIL-specific canonical behavior in our own wrapper.

### Candidates

#### Option A: `num-complex` (recommended)

- Crate: `num-complex`
- Fit:
  - Provides standard complex number type and arithmetic primitives.
  - Broadly used and maintained in the Rust numeric ecosystem.
  - Matches our future needs for advanced complex operations better than hand-rolling.
- Integration shape:
  - Keep `CanonicalComplex32` / `CanonicalComplex64` as MeTTaIL public runtime types for Eq/Hash/Ord/Display/Ascent compatibility.
  - Use `num_complex::Complex32` / `num_complex::Complex64` internally for arithmetic/function implementations.
- Pros:
  - Avoids re-implementing advanced complex math.
  - Better long-term maintainability as feature surface grows.
  - Clean separation: canonical semantics in wrapper, math in dependency.
- Cons:
  - Adds one dependency to `mettail-runtime`.
  - Still requires wrapper-level canonicalization and trait policy.

#### Option B: No new dependency (manual implementation)

- Fit:
  - Works for minimal v1 arithmetic only.
- Pros:
  - Zero dependency cost.
  - Full control over implementation details.
- Cons:
  - Expensive and risky for upcoming advanced functions.
  - Higher maintenance burden and more room for numerical edge-case mistakes.

#### Option C: Heavy linear algebra / scientific stack crates

- Fit:
  - Overkill for scalar complex values in language runtime.
- Pros:
  - Rich functionality for matrix/vector domains.
- Cons:
  - Unnecessary dependency footprint and complexity for current project scope.

### Recommendation

Adopt `num-complex` now, but keep canonical wrapper types as runtime boundary types:

- `CanonicalComplex32` / `CanonicalComplex64` own canonical Eq/Hash/Ord/Display/BoundTerm behavior.
- `num_complex::Complex32` / `num_complex::Complex64` power arithmetic and upcoming advanced functions.

This gives us immediate stability for Ascent integration and a future-proof base for advanced complex functionality.

## Proposed Representation

### Runtime Type

Add runtime canonical wrappers as newtypes over `num_complex::Complex32/Complex64`:

- `runtime/src/canonical_complex.rs`
- `pub struct CanonicalComplex32(num_complex::Complex32)`
- `pub struct CanonicalComplex64(num_complex::Complex64)`

Rationale:

- Reuses existing float canonicalization behavior (NaN, signed zero normalization rules already encapsulated) for both 32-bit and 64-bit variants.
- Keeps Eq/Hash/Ord requirements Ascent-compatible via canonical components.
- Uses native `num_complex::Complex32` / `num_complex::Complex64` arithmetic/function implementations directly.
- Preserves MeTTaIL-specific canonical semantics at the wrapper boundary by canonicalizing values in wrapper constructors/conversions.

Expose in `runtime/src/lib.rs`:

- `pub use canonical_complex::{CanonicalComplex32, CanonicalComplex64};`

### Semantics

- **Equality:** Component-wise equality on canonical real/imaginary parts.
- **Display (canonical):**
  - `a+bi` when `im >= 0`
  - `a-bi` when `im < 0`
  - Preserve float display style used by `CanonicalFloat64` where possible.
- **Zero check:** `re == 0 && im == 0` (in wrapper precision).
- **Arithmetic:** `+`, `-`, unary `-`, `*`, `/` (with zero-denominator handling strategy below).
- **Ordering policy:** deterministic lexicographic order `(re, im)` for `Ord` impl (required for stable relation behavior).

### Precision Policy

- The complex category precision should be chosen explicitly by language authors:
  - `![mettail_runtime::CanonicalComplex32] as Complex` or
  - `![mettail_runtime::CanonicalComplex64] as Complex`.
- Constructor/eval inputs should match category precision:
  - if `Complex = CanonicalComplex32`, constructor should consume `Float32` inputs;
  - if `Complex = CanonicalComplex64`, constructor should consume `Float64` inputs.
- If mixed-precision language categories are introduced, conversion must be explicit (no hidden widening/narrowing).

## Surface Syntax Proposal (v1)

Initial parsing form:

1. **Constructor form only:** `complex(<real>, <imag>)`

Display/result form:

- Canonical display is `a+bi` / `a-bi`.
- Parser sugar for `<num>i` and `a+bi` is deferred to a follow-up phase.

This keeps parser changes minimal in v1 while still providing user-friendly normal-form output.

## Language Integration

### Calculator (`languages/src/calculator.rs`)

Add type:

- `![mettail_runtime::CanonicalComplex64] as Complex` (default example)
- Also supported by design: `![mettail_runtime::CanonicalComplex32] as Complex`

Add terms:

- `ProcComplex . c:Complex |- c : Proc ;`
- `ComplexCtor . re:Float, im:Float |- "complex" "(" re "," im ")" : Complex ![...] fold;`
- Arithmetic:
  - `AddComplex`, `SubComplex`, `MulComplex`, `DivComplex`, `NegComplex`
- Equality:
  - `EqComplex`, `NeComplex`

Add `Proc` conversions:

- `ProcToBool`: complex zero/non-zero behavior.
- `ProcToStr`: string representation of complex.

v1 casts/conversions:

- Keep to core conversions only in v1 (Bool/Str projections and constructor path).
- Additional numeric cast bridges can be added later.

### RhoCalc (`languages/src/rhocalc.rs`)

Add type and cast:

- `![mettail_runtime::CanonicalComplex64] as Complex` (default example)
- Also supported by design: `![mettail_runtime::CanonicalComplex32] as Complex`
- `CastComplex . c:Complex |- c : Proc;`

Add `Proc` fold operations in existing style:

- In `Add`, `Sub`, `Mul`, `Div`, `NegProc`, `Eq`, `Ne` match arms for `Proc::CastComplex`.
- Keep strict same-type operation behavior (no implicit Int/Float/Complex mixed arithmetic in v1).
- For mismatch cases, preserve current behavior: return `Proc::Err`.

## Error Handling Strategy (v1)

Division by zero for complex numbers is explicit-error in both languages:

- `calculator`: explicit `Err` normal-form style for `Complex`.
- `rhocalc`: return `Proc::Err` for divide-by-zero complex denominator.

Implementation detail:

- Add `checked_div` on both wrappers:
  - `CanonicalComplex32 -> Option<Self>`
  - `CanonicalComplex64 -> Option<Self>`
- Call sites choose language-specific error projection.

## Numeric Cast and Conversion Plan

Initial v1 conversions:

- `Complex -> Bool`: zero check.
- `Complex -> Str`: canonical display.

Deferred conversions (post-v1):

- `Complex -> Float/Int/...` only when `imag == 0`; otherwise cast error.
- Parsing numeric strings like `"3+4i"` through cast pipelines.
- Real-to-complex conversion helpers (`x -> complex(x, 0)`) if needed for richer cast interoperability.

## Rewrite/Congruence Additions

Both languages will need congruence rules for each new complex operation, following existing per-operator patterns:

- `AddComplexCongL/R`, `SubComplexCongL/R`, `MulComplexCongL/R`, `DivComplexCongL/R`, `NegComplexCong`
- Equality/conversion congruence as needed for parse-to-normal-form reachability.

For `rhocalc`, add congruence rules in line with current `AddCongL/R`, `DivCongL/R`, etc., if new term constructors are introduced.

## Test Plan

### Runtime Unit Tests

- `CanonicalComplex32` and `CanonicalComplex64`:
  - constructor/getters
  - equality/hash consistency
  - add/sub/mul/div
  - division-by-zero returns `None`
  - display stability

### Calculator Tests (`languages/tests/calculator.rs`)

- parse and eval:
  - `complex(1.0, 2.0)`
  - `complex(1.0, 2.0) + complex(3.0, -1.0)`
  - multiplication/division sanity
- comparisons:
  - `==`, `!=`
- proc conversion:
  - `bool(complex(0.0, 0.0))` -> false
  - `bool(complex(0.0, 1.0))` -> true
  - `str(complex(...))`
- error:
  - division by zero denominator path

### RhoCalc Tests (`languages/tests/rhocalc_tests.rs`)

- arithmetic inside `{ ... }` proc context.
- error-on-type-mismatch behavior preserved.
- comm/congruence smoke tests where complex expressions are nested and reduced.

## Rollout Plan

1. **Runtime foundation**
   - Add `CanonicalComplex32` and `CanonicalComplex64` + tests + re-export.
   - Add `num-complex` dependency in `runtime/Cargo.toml`.
2. **Calculator integration**
   - Add category/terms/rewrites/tests.
3. **RhoCalc integration**
   - Add type/casts/ops/rewrite coverage/tests.
4. **Casting expansion (optional)**
   - Add explicit conversion pipelines for complex where required.
5. **Docs/examples**
   - Add examples in REPL sample files for both languages.

This keeps each step small and verifiable with `cargo test`, `cargo clippy`, and `cargo fmt`.

## Accepted v1 Decisions

1. Display canonical normal forms as `a+bi` / `a-bi`.
2. Enforce strict same-type arithmetic (no implicit promotion in v1).
3. Make complex divide-by-zero explicit error (no panic path).
4. Include only core arithmetic/equality/conversions in v1.
5. Keep parser constructor-only in v1; add `bi` / `a+bi` syntax later as sugar.

## Next Step

Implement phase 1 according to this document:

1. Runtime `CanonicalComplex32` and `CanonicalComplex64` (newtype wrappers over `num_complex`).
2. Calculator integration.
3. RhoCalc integration with matching strict/error semantics.

> Precision note: language authors should be able to choose either 32-bit or 64-bit complex payloads in `types { ... }`, mirroring how Float precision selection works today.

## Design Revisit Notes (num-complex)

- Keep `num-complex` as implementation detail, not exposed as language/runtime public category type.
- Enforce canonicalization only at wrapper boundaries (`new`, `from_parts`, conversions), then delegate math operations to wrapped `num_complex` values.
- Prefer wrapper-local utility methods for advanced functions (`sin`, `cos`, `exp`, `ln`, etc.) so language code stays independent of crate internals.
- Maintain strict same-type semantics at language level even if `num-complex` could technically interoperate with scalar values.
