# Signed BigInt Library Selection

**Status:** Implemented — `num-bigint` with a **`Copy`-compatible** runtime wrapper `CanonicalBigInt` in `mettail-runtime` (`runtime/src/canonical_bigint.rs`); integer literals flow through `prattail::parse_int_lit` (`prattail/src/int_lit.rs`) and per-language `literals` blocks (e.g. `…n` for `BigInt` in Calculator / RhoCalc).

## Context

We need to add **signed bigint literals** in MeTTaIL (`<digits>n`).

The solution should be:

- consistent with current integer literal architecture (`IntLit`, suffix parsing, strict typing),
- portable across developer and CI environments,
- maintainable for long-term language evolution (including future BigRat support),
- and fast enough for REPL and rule-evaluation workflows.

## Candidate libraries

The list below focuses on bigint suitability for this project (dynamic signed integers for parser/runtime values).

### 1) `num-bigint`

- Type model: dynamic-width `BigInt`/`BigUint`.
- Implementation: pure Rust, optional `no_std`.
- Ecosystem: very high adoption and strong integration with `num-traits`.
- Fit for this use case: very strong.

Pros:
- Stable API and broad compatibility.
- Large ecosystem and many integrations.
- Good enough performance for language-runtime workloads.

Cons:
- Not the fastest in raw arithmetic benchmarks versus GMP-backed options.

### 2) `ibig`

- Type model: dynamic-width `IBig`/`UBig`.
- Implementation: pure Rust, `no_std`.
- Performance: often among the fastest pure-Rust bigint implementations.

Pros:
- Strong pure-Rust performance profile.
- Clean API for integer arithmetic.

Cons:
- Smaller ecosystem footprint than `num-bigint`.
- Potentially higher integration effort than the `num` ecosystem path.

### 3) `rug` (GMP/MPFR/MPC bindings)

- Type model: dynamic-width integer/rational/float/complex.
- Implementation: Rust wrapper over native C libraries (GMP family).
- Performance: typically highest absolute performance in bigint benchmarks.

Pros:
- Best raw arithmetic throughput in many workloads.
- Rich numeric stack (integer + rational + float).

Cons:
- Native dependency/toolchain complexity (linking/packaging/licensing constraints).
- Harder cross-platform and CI reproducibility compared to pure Rust.
- Heavier operational burden for a parser/runtime crate.

### 4) `num-bigint-dig`

- Fork focused on cryptography-related additions (e.g., prime-related helpers).
- Still a dynamic bigint library.

Pros:
- Extra crypto-oriented functionality.

Cons:
- Fork divergence risk versus `num-bigint`.
- Added features are mostly outside current language-literal needs.

### 5) `crypto-bigint`

- Type model: fixed-width unsigned integers via const generics.
- Focus: constant-time cryptographic arithmetic.

Why not for this task:
- We need dynamic signed bigint values for user literals, not fixed-width crypto integers.

### 6) `ramp`

- Historically high-performance bigint.
- Maintenance status is effectively inactive/unmaintained.

Why not:
- Maintenance risk is too high for a core numeric backend.

### 7) `scientific`

- Arbitrary-precision scientific-number focus.

Why not as primary bigint backend:
- Different abstraction target (scientific representation), not standard dynamic signed bigint.

### 8) `fraction`

- Fraction/rational-centric crate; bigint is optional backend detail.

Why not as primary bigint backend:
- Solves a different layer (rationals) rather than core bigint literal representation.

## Benchmark perspective

External benchmarks generally support:

- `rug`/GMP: fastest absolute arithmetic throughput.
- `ibig`: strongest pure-Rust contender.
- `num-bigint`: commonly slower than those top contenders, but widely used and robust.

For this project, benchmark ranking must be weighed against integration cost and operational complexity:

- literal parsing and AST conversion are usually not dominated by huge bigint arithmetic loops,
- portability and low-friction contributor setup are high-value.

## Decision

Choose **`num-bigint`** as the implementation backend for Signed BigInt now.

Rationale:

1. It directly matches dynamic signed integer semantics.
2. It gives the best balance of maturity, ecosystem fit, and implementation simplicity.
3. It avoids native toolchain/linking complexity (`rug`/GMP) while staying pure Rust.
4. It keeps the implementation path straightforward for parser/literal integration.

## Optional future optimization path

If future profiling shows bigint arithmetic as a dominant bottleneck:

1. introduce a thin internal bigint adapter trait/type alias layer;
2. keep `num-bigint` as default backend;
3. evaluate optional alternative backend(s), with `rug` (native/GMP) as an opt-in high-performance profile.

This should be done only after workload-driven profiling demonstrates clear need.

## Implementation (done)

With backend choice fixed to `num-bigint`, the tree includes:

- `prattail`: `IntLit::BigInt` and `parse_int_lit` / suffix handling for large integers.
- `mettail-runtime`: `CanonicalBigInt` for `BoundTerm` / Ascent-friendly literals.
- Languages: e.g. `![mettail_runtime::CanonicalBigInt] as BigInt` and a `BigInt` literal pattern ending in `n` in `languages/src/calculator.rs`, `languages/src/rhocalc.rs`.
- Tests: language and prattail tests for parsing and evaluation of large literals.

## See also

- [Signed BigRat design](./signed-bigrat-design.md) — rationals, `…r` literals, `fraction`, and `CanonicalBigRat`.
