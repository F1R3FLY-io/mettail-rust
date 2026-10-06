# Exact native DDL literal contract

This document describes the implemented numeric literal boundary for inline
MeTTaIL DDL in Rholang. A projection row's host abstract-syntax-tree (AST)
leaf is a typed literal. Its spelling is parsed by the generated Rholang
grammar, lowered as structured data, and validated as that same carrier.
There is no cross-carrier numeric conversion or parse of process text at this
boundary.
The [frontend admission contract](rholang-frontend-admission-contract.md) covers
the surrounding source admission; this document covers the numeric leaves.

## Source spellings and identities

The generated `Int`, `BigInt`, `BigRat`, `Fixed`, and `Float` categories are
declared in [the Rholang grammar](../../languages/src/rholang.rs). The separate
[standalone DDL lexer](../../mettail-elab/src/lex.rs) recognizes the corresponding
spellings for its own entrypoint. A sign abutting a numeral belongs to that
literal's spelling. Radix prefixes (`0b`, `0o`, `0x`) and underscores in digit
runs are available for integer and rational components, subject to each
category's pattern; a negative radix rational does not have a single folded
literal reading. Decimal fixed and float forms accept digit separators. The
generated `Float` spelling admits a decimal point or exponent and an optional
`f64` suffix, including leading-dot forms.
Its literal parser canonicalizes negative zero. These descriptions are of
literal categories, not a promise that every expression containing a numeral
is a projection literal.

| Generated category | Representative spelling | Typed structural value | Identity rule |
| --- | --- | --- | --- |
| `Int` | `42`, `-7i64`, `5u32` | `Integer(i128)` in the canonical value model, restricted to Rholang's `i64` native literal range | The `Int` leaf stays an integer leaf. An out-of-range `Integer` is refused by the renderer; an explicit `BigInt` value is required. |
| `BigInt` | `9223372036854775808n`, `0x2an` | `BigInt(Vec<u8>)` | Minimal signed big-endian two's-complement bytes, including a sign-preserving leading `00` when needed. The generated grammar also admits an **unsuffixed** integer outside `i64` as `BigInt`. |
| `BigRat` | `7r`, `-3r/4r` | `BigRat { numerator, denominator }` | Both components use minimal signed big-endian bytes; denominator is positive and the fraction is reduced. The composite `Nr/Dr` form is a generated-language extension for exact nonintegral values. |
| `Fixed` | `1.25p2`, `12p1` | `FixedPoint { unscaled, scale }` | The signed unscaled integer and declared `u32` scale are both retained. Equal numeric magnitude at a different scale is a different structural value. |
| `Float` | `.5f64`, `1e2`, `-0.0` | `FloatBits(u64)` | Finite IEEE-754 binary64 bits are retained after canonicalization; negative zero becomes positive zero. A nonfinite value has no admitted source literal here. |

For `Fixed`, the represented value is:

```math
v = u \times 10^{-s}
```

Here `u` is the signed unscaled integer and `s` is the declared scale. For
example, `1.25p2` produces `unscaled = 125, scale = 2`; `1.2p1` produces
`unscaled = 12, scale = 1`. The [fixed literal parser](../../runtime/src/fixed_lit.rs)
rejects a positive scale smaller than the mantissa's fractional precision;
its special `p0` path rounds a fractional mantissa half away from zero. Exact
round-trip emission uses a decimal with precisely the stored scale, so it does
not depend on that rounding path.

The [rational parser](../../prattail/src/rational_lit.rs) rejects zero
denominators and reduces `2r/4r` to the stored numerator `1`, denominator `2`.
Canonical admission additionally requires positive denominator and coprime
components; it does not silently repair a malformed structural payload.

## Structural route

| Boundary | What it does |
| --- | --- |
| Generated Rholang parse | Builds typed `DdlRuleAstInteger`, `DdlRuleAstBigInt`, `DdlRuleAstBigRat`, `DdlRuleAstFixed`, or `DdlRuleAstFloat` leaves from native category literals. |
| [DDL lower plan](../../rholang-runtime/src/ddl_ast.rs) | Accepts the matching native literal variant, extracts exact signed bytes, scale, or float bits, and builds native `GBigInt`, `GBigRat`, `GFixedPoint`, `GDouble`, or `GInt` data in a tagged DDL wire node. It rejects a nonliteral term and checks the `Int` range and float finiteness. The same plan can produce a canonical `RhoValue` for comparison. |
| [DDL wire decoder](../../mettail-elab/src/wire.rs) | Requires `ast-integer`, `ast-bigint`, `ast-bigrat`, `ast-fixed`, and `ast-float` to carry the corresponding typed payload, with exactly one child. It checks `i64` width, canonical signed bytes, reduced rational form, and finite canonical float bits. A `String` with decimal-looking text does not satisfy a numeric leaf. |
| [Theory compiler](../../mettail-elab/src/theory_compile.rs) | Copies admitted scalar payloads into typed theory literals and retains their carrier; it does not narrow arbitrary-precision values to an `i64` or convert them through floating point. |

The native runtime decoder of closed ordinary values likewise maps
`GBigInt`, `GBigRat`, `GFixedPoint`, and `GDouble` to distinct `RhoValue`
variants and checks arbitrary-precision byte payloads before installation
([runtime value decoder](../../rholang-runtime/src/language_install.rs)).
The typed source `Data(v)` path and DDL projection AST path share the
canonical value model, but have different shape checks. In particular,
generic `admit_canonical_value` checks signed integer, rational, and resource
invariants; the projection decoder adds its finite, canonical float-bit rule.
Do not infer that every arbitrary `FloatBits` value is a valid projection
literal merely because the generic value walker can visit it.

These checks occur while source is parsed, lowered, and compiled for language
installation. The later installed language consumes the resulting typed
theory literals; it is not asked to reinterpret numeric source text. A
projection row containing a computed expression is therefore not admitted as
a numeric literal leaf by this route.

The signed-byte invariant is minimal two's-complement big-endian form:
empty input, redundant positive `00`, and redundant negative `ff` are
refused. Zero is one byte, `00`; positive `128` is `00 80`; negative `-3` is
`fd`. This makes byte equality agree with integer equality at this wire
boundary ([canonical value admission](../../mettail-elab/src/canonical.rs)).

## Renderer and normalization seam

The [Rholang value literal renderer](../../mettail-elab/src/rholang_literal.rs)
is migration/bootstrap tooling for an already typed canonical value; inline
DDL itself is parsed once by the generated Rholang parser. The renderer emits
`n` for `BigInt`, `Nr/Dr` for `BigRat`, `p<scale>` for `Fixed`, and a decimal
point on integral `Float` values (for example `0.0`) so a reader cannot elect
the `Int` carrier. It first checks the canonical value and enforces a separate
output-byte limit. It rejects an `Integer` outside `i64` rather than changing
its type to `BigInt`; rejects nonfinite float bits; and rejects raw negative-zero
bits rather than printing a spelling that the native float parser would
normalize. By contrast, parsing source `-0.0` legitimately yields positive-zero
bits through `CanonicalFloat64`.

The relevant exactness property is typed value equality after render and
read, within the renderer's admitted domain. Textual identity is not required:
radix prefixes and digit separators can disappear; rationals can reduce;
`-0.0` normalizes; and fixed-point text can be laid out differently while
retaining `unscaled` and `scale`.

## Limits and trust boundary

These literals are untrusted input. [Canonical value admission](../../mettail-elab/src/canonical.rs)
uses an iterative walk and currently bounds a value to 1,000,000 nodes and
1,000,000 collection items, each string to 4 MiB and all strings to 16 MiB,
each byte payload to 16 MiB and all byte payloads to 64 MiB. The DDL parser
and decoder enforce a structural depth of 256; the runtime's closed-value
decoder has its own node, depth, byte, and collection limits, including a
128 MiB candidate-encoding ceiling. The renderer separately caps complete
literal output at 128 MiB, checks size arithmetic, and reports allocation
failure. Structural lowering charges work and payload bytes through its
reservation interface. These are resource controls, not permissions to
evaluate a literal or to install a language. Installation still applies the
normal schema, trust, and authority checks.

## Evidence and scope

The repository contains direct checks for this contract:

- [Generated-to-wire receipt tests](../../rholang-runtime/src/ddl_ast/receipt_tests.rs) compare generated typed literals with both native wire expressions and canonical values, including property tests for `BigInt`, `BigRat`, `Fixed`, and finite `Float`.
- [Standalone parser tests](../../mettail-elab/src/parse.rs) check exact rendered/read values and property-test carrier, signed-byte, reduced-rational, scale, and canonical finite-float round trips.
- [Projection wire tests](../../mettail-elab/src/wire.rs) accept typed leaves and refuse wrong types, nonminimal signed bytes, unreduced or zero-denominator rationals, nonfinite floats, and negative-zero float bits.
- [Renderer tests](../../mettail-elab/src/rholang_literal.rs) pin native scalar spelling, out-of-range `Int` refusal, negative-zero refusal, map ordering, and output limits.
- [Generated Rholang entrypoint test](../../rholang-runtime/src/language_install.rs) checks that a rendered `Data` theory installs with the same fingerprint as its canonical value without a source reparse at lowering.

This is a source-and-test inventory, not a claim that this document ran those
tests. Arithmetic operations and explicit numeric casts have their own
semantics; their existence does not authorize coercion at a DDL literal leaf.
