---
name: Bitwise ops for integer types
overview: Add bitwise AND/OR/NOT for integer-like types in `Calculator` then `RhoCalc`, implemented in each language’s `terms` (and the minimal congruence rewrites needed for evaluation), with helper functions for `CanonicalBigInt`, `CanonicalBigRat`, and the `Fixed` type.
todos:
  - id: research-deps
    content: Check whether `num-integer` (or equivalent gcd/lcm) is already available; pick minimal approach for lcm/gcd on `BigInt`.
    status: pending
  - id: calc-helpers-and-terms
    content: Add helper fns + `terms` rules for Int/UInt32/BigInt/BigRat bitwise ops in `languages/src/calculator.rs`.
    status: pending
  - id: calc-rewrites
    content: Add congruence rewrites for the new Calculator bitwise terms in `languages/src/calculator.rs`.
    status: pending
  - id: rhocalc-helpers-and-terms
    content: Add helper fns + `terms` rules on `Proc` for bitwise ops in `languages/src/rhocalc.rs` (dynamic dispatch, return `Proc::Err` on mismatch).
    status: pending
  - id: rhocalc-rewrites
    content: Add congruence rewrites for the new RhoCalc bitwise terms in `languages/src/rhocalc.rs`.
    status: pending
  - id: verify
    content: Compile/test the workspace and run any existing language eval checks relevant to the new operators.
    status: pending
isProject: false
---

## Scope

- Implement bitwise operations for all integer(-like) types currently present in each language.
  - `Calculator`: `Int` (`i32`), `UInt32` (`u32`), `BigInt` (`mettail_runtime::CanonicalBigInt`), `BigRat` (`mettail_runtime::CanonicalBigRat`), `Fixed` (fixed-point).
  - `RhoCalc`: same set (including `Fixed`), but operations are defined on `Proc` via dynamic dispatch.

## Operator surface syntax (proposed default)

- `a "&" b` for bitwise AND
- `a "|" b` for bitwise OR
- `"~" a` for bitwise NOT (unary prefix)
  - Note: this requires deleting the existing `CustomOp` in `Calculator`, which currently uses `"~"`.

## Semantics

- `**Int`/`UInt32**`: Rust’s built-in `&`, `|`, `!`.
- `**BigInt**`: bitwise ops applied to `num_bigint::BigInt` values underlying `CanonicalBigInt`.
  - Use `CanonicalBigInt::from((a.get() OP b.get()).clone())` style helpers to return a new canonical handle.
- `**BigRat**`:
  - Reduce to a common denominator, scale numerators, apply bitwise op to the **scaled numerators**, keep the common denominator:
    - Let r_1=n_1/d_1, r_2=n_2/d_2, D=\mathrm{lcm}(d_1,d_2)
    - N_1=n_1\cdot(D/d_1), N_2=n_2\cdot(D/d_2)
    - AND/OR result: (N_1OPN_2)/D
    - NOT result: (\sim N_1)/d_1
  - Build result with `CanonicalBigRat::try_from_nd(num, den)`; denominator is guaranteed non-zero.
- `**Fixed`**:
  - Same rule as `BigRat`’s common-denominator story, but the operation is done on **numerators only** after alignment, preserving the chosen fixed precision.
  - Concretely: lift both fixed values to a common scale 10^p where p=\max(p_1,p_2), interpret them as rationals with denominator 10^p, then apply bitwise op to aligned numerators and keep denominator 10^p.

## Implementation details

### `Calculator` (`languages/src/calculator.rs`)

- Add Rust helper functions above `language! { ... }`:
  - `fn cbigint_and(a: CanonicalBigInt, b: CanonicalBigInt) -> CanonicalBigInt`
  - `fn cbigint_or(...) -> CanonicalBigInt`
  - `fn cbigint_not(a: CanonicalBigInt) -> CanonicalBigInt`
  - `fn cbigrat_and(a: CanonicalBigRat, b: CanonicalBigRat) -> CanonicalBigRat` (and/or/not variants)
    - Use `a.get().numer()`, `a.get().denom()` (available per `runtime/src/canonical_bigrat.rs`).
    - Use gcd/lcm on `BigInt` (via `num_integer::Integer` or manual gcd) to compute common denominator.
  - Add `Fixed` helper(s) in the same style (exact function signatures depend on the concrete `Fixed` representation), implementing the “align precision then bitwise on numerators” rule.
- Add `terms` rules near other numeric ops:
  - `BitAndInt . a:Int, b:Int |- a "&" b : Int ![a & b] ...`
  - `BitOrInt ...`
  - `BitNotInt . a:Int |- "~" a : Int ![!a] ...`
  - Same for `UInt32`.
  - `BigInt` rules call helpers: `![cbigint_and(a,b)]`, etc.
  - `BigRat` rules call helpers: `![cbigrat_and(a,b)]`, etc.
  - Add `Fixed` rules using the same operator tokens, producing a `Fixed` whose precision is the common precision (typically `max(p1,p2)`).
- Add corresponding congruence rewrites in `rewrites { ... }` (mirroring existing patterns like `AddIntCongL/R`, `NotCong`, etc.).
- Delete `CustomOp` (the existing `a "~" b` term) and delete its associated congruence rewrites (`CustomOpCongL`, `CustomOpCongR`).

### `RhoCalc` (`languages/src/rhocalc.rs`)

- Add helper functions (same file, above `language!`) for:
  - `CanonicalBigInt` bitwise ops (as above).
  - `CanonicalBigRat` common-denominator bitwise logic (as above).
  - `Fixed` alignment + bitwise helpers (precision alignment then numerator op).
- Add `terms` rules that operate on `Proc` (like existing `Add`, `Sub`, etc.), using pattern matches:
  - `BitAnd . a:Proc, b:Proc |- a "&" b : Proc ![{ match (&a,&b) { ... } }] fold;`
  - `BitOr ...`
  - `BitNot . a:Proc |- "~" a : Proc ![{ match &a { ... } }] fold;`
  - Cases to support:
    - `CastInt(Int::NumLit(..))`
    - `CastUInt32(UInt32::NumLit(..))`
    - `CastBigInt(BigInt::NumLit(..))`
    - `CastBigRat(BigRat::RatLit(..))`
    - `CastFixed(Fixed::...)` (exact constructor depends on the `Fixed` AST/literal form)
    - Otherwise return `Proc::Err`.
- Add congruence rewrites in `rewrites { ... }` for the new term constructors (following existing `AddCongL/R`, `NotCong`, etc.).

## Files to change

- `[languages/src/calculator.rs](languages/src/calculator.rs)`
- `[languages/src/rhocalc.rs](languages/src/rhocalc.rs)`
- These same files are expected to contain the `Fixed` type; bitwise support will be added there.
- Potentially add a small dependency if missing for gcd/lcm:
  - `num-integer` (only if not already in workspace dependencies).

```
Verification
```

- Build/tests after implementation:
  - `cargo test` (or at least compile `languages` + `runtime`).
- Add comprehensive tests (and at minimum the following evaluation checks, if you have a test harness already):
  - `1 & 3 == 1`, `~0 == -1` (signed Int), `1u32 & 3u32 == 1u32`.
  - `1n & 3n == 1n`.
  - `fraction(1n,3n) & fraction(3n,4n)` using the chosen `BigRat` semantics.
- Add semantic “alignment” examples (these are the reference calculations the helper functions must reproduce):
  - Fixed-point:
    - `12.2p1 | 7.01p2`
      - Align precision to `p2`: `12.2p1 = 12.20p2`
      - As rationals: `12.20p2 = 1220/100`, `7.01p2 = 701/100`
      - Bitwise-or on aligned numerators: `(1220 | 701)/100 = 1789/100 = 17.89p2`
    - Same alignment rule for `&`:
      - `12.2p1 & 7.01p2 = (1220 & 701)/100 = 132/100 = 1.32p2`
    - Bitwise NOT (no alignment needed; operate on the numerator under its own precision):
      - `~12.2p1 = ~(122/10) = (~122)/10 = (-123)/10 = -12.3p1`
      - `~7.01p2 = ~(701/100) = (~701)/100 = (-702)/100 = -7.02p2`
  - BigRat (fractional):
    - `(7r/12r) | (11r/16r)`
      - `gcd(12,16)=4`, `lcm(12,16)=48`
      - Align: `7/12 = 28/48`, `11/16 = 33/48`
      - Result: `(28 | 33)/48 = 61/48`
    - Same alignment rule for `&`:
      - `(7r/12r) & (13r/16r)`
        - `gcd(12,16)=4`, `lcm(12,16)=48`
        - Align: `7/12 = 28/48`, `13/16 = 39/48`
        - Result: `(28 & 39)/48 = 4/48 = 1/12 = (1r/12r)`
    - Bitwise NOT (no alignment needed):
      - `~(7r/12r) = (~7)/12 = (-8)/12 = (-2r/3r)`

## Additional information

- `BigRat` bitwise ops apply to **scaled numerators** after moving to a common denominator.
- `Fixed` bitwise ops apply to **aligned numerators** after moving to a common precision/denominator (per your example).
- `CustomOp` will be deleted so `"~"` can be used as bitwise NOT; boolean `"not"` remains boolean-only.

