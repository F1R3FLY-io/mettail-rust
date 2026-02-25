# 02-24: RhoCalc test structure

Replaced the monolithic `rhocalc_tests.rs` (flat list of tests + manual `main()` runner) with a modular framework.

## Helpers

- `fresh()` — clears var cache (called once per test entry point)
- `run(input)` — parse + run_ascent via `Language` trait
- `assert_reduces_to(input, expected)` — normal form matches expected (handles PPar multiset ordering)
- `assert_min_rewrites(input, n)` / `assert_no_rewrites(input)` / `assert_initial_rewrites(input)`

## Modules (67 tests)

| Module | # | What it covers |
|---|---|---|
| `comm` | 8 | Single/multi-input, join patterns, remaining parallel |
| `new_and_extrusion` | 8 | PNew parsing, NewCong, extrusion forward/blocked |
| `congruence` | 6 | ParCong, NewCong, Add/comparison propagation |
| `exec` | 3 | Drop-quote, QuoteDrop equation |
| `native_ops::arithmetic` | 7 | Int/float add/sub/mul/div, chaining, negatives |
| `native_ops::comparison` | 7 | ==, !=, >, <, >=, <= |
| `native_ops::boolean` | 6 | not, and, or |
| `native_ops::string` | 2 | concat, len |
| `native_ops::type_conversion` | 4 | int/float/bool/str casts |
| `parsing` | 10 | All term constructors + type inference |
| `beta` | 3 | Dollar-syntax beta-reduction |
| `type_inference` | 3 | Bound variable type inference |

## File

`languages/tests/rhocalc_tests.rs`
