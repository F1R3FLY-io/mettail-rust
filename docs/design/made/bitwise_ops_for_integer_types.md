---
name: Bitwise ops for integer-like types
overview: Implemented bitwise AND, OR, and NOT semantics in Calculator and Rholang.
status: implemented
last_updated: 2026-08-04
isProject: false
---

# Bitwise operations for integer-like carriers

Calculator and Rholang expose the word operators `bitand`, `bitor`, and `bitnot`. The generated
terms and congruence rules live in `languages/src/calculator.rs` and `languages/src/rholang.rs`;
shared carrier behavior lives in `runtime`.

## Surface and disposition

| Carrier | `bitand` / `bitor` | `bitnot` |
|---|---|---|
| `Int`, `UInt32` | Rust integer operation | Rust integer complement |
| `CanonicalBigInt` | `BigInt` operation | `BigInt` complement |
| `CanonicalBigRat` | common-denominator numerator operation | numerator complement |
| `CanonicalFixedPoint` | same-scale unscaled-integer operation | unscaled-integer complement |

Rholang performs dynamic carrier dispatch and returns its `error` term for unsupported carrier
pairs. Calculator has carrier-specific term constructors, so an unsupported pair has no successful
fold rule.

## BigRat semantics

For `r1 = n1/d1` and `r2 = n2/d2`, let `D = lcm(d1, d2)`,
`N1 = n1(D/d1)`, and `N2 = n2(D/d2)`. Binary operations return
`(N1 op N2)/D`, reduced by `CanonicalBigRat`. Unary `bitnot` returns `(!n1)/d1`.

Examples:

- `(7/12) bitor (11/16) = (28 bitor 33)/48 = 61/48`.
- `(7/12) bitand (13/16) = (28 bitand 39)/48 = 1/12`.
- `bitnot (7/12) = (-8)/12 = -2/3`.

## Fixed-point semantics

A fixed-point value is the structural pair `(unscaled, places)`. Binary bitwise operations are
defined only when both declared scales are equal. At equal scale `P`, they apply the integer
operation to the unscaled payloads and preserve `P`:

```math
(u_a, P)\;\mathsf{op}\;(u_b, P) = (u_a\;\mathsf{op}\;u_b, P)
```

Mismatched scales are refused. Decimal rescaling is deliberately not used: multiplying a mantissa
by a power of ten is not a bit shift, and upstream Rholang provides no fixed-point bitwise rule that
would justify silently changing either operand. Programs that intend a common scale must say so
with `fixed(value, places)` first.

Unary `bitnot` does not need a second scale and returns `(!unscaled, places)`.

## Verification

- `runtime/src/canonical_fixed_point.rs` tests the checked same-scale helpers.
- `languages/tests/fixedpoint_scale_dedup_ab.rs` rejects mixed-scale Calculator operations.
- `languages/tests/rholang_arith_carrier_matrix.rs` covers Rholang carrier dispatch and refusal.
- The ordinary generated congruence suites ensure children continue to reduce under each operator.

This file replaces the original implementation plan, whose proposed symbolic operators and
automatic fixed-point scale alignment were never the final language semantics.
