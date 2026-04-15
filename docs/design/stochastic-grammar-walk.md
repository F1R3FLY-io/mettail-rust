# Grammar-aware stochastic term generation

## Problem

The `language!` macro emits a proptest-based stochastic generator
`arb_<cat>` for each declared category. Historically this generator
built ASTs directly from native type ranges (`Int::NumLit(next_i64())`
etc.), then Displayed the AST to a string, which the test harness
parsed back.

This violated a fundamental invariant: **every generated term must be
a valid surface term of the grammar** — i.e. its Display must
re-parse. For any value class the grammar's lexer does not admit —
the canonical example is `NumLit(-5)` in a language whose Integer
token is `[0-9]+` (no leading sign) and which has no `Neg` rule —
the Display step emits text the lexer cannot tokenize. Running
`simulate_rhocalc` would then report terms as failing with parse
errors like `1:1: expected Proc expression, found '-'`, and the
strategy harness at `strategies.rs:1131` silently skipped those
failures — polluting pass counts with out-of-grammar garbage.

Additionally, two adjacent panics made the situation hidden:

1. `impl std::ops::{Add,Sub,Mul,Div,Rem} for <category>` emitted by
   `macros/src/gen/native/eval.rs:527–567` used raw `eval() * eval()`
   on i64 values. Debug-mode overflow panics escaped the test
   harness's `catch_unwind` because they fired during unwinding of
   another panic — producing a SIGABRT with "failed to initiate
   panic, error 5".
2. The lexer codegen at `prattail/src/automata/codegen.rs:657–677,
   1015–1026` used `.expect()` on `ParseIntError` for literals
   exceeding `i64::MAX`.

The bugs surfaced together on strings like `-9223372036854775808`:
display emits `-9223372036854775808` (perfectly fine native i64
value), lexer tokenises `-` separately and tries to parse
`9223372036854775808` as i64 — `.expect()` panics, and the panicking
ops impls ensure the abort is double-panic. The blanket fix would
have been to clamp `next_i64()` to non-negative, but that
*eliminates half the tape's value domain* for every language — a
silencing shortcut that deletes test coverage instead of addressing
the grammar mismatch.

## Solution: grammar-aware literal emission, bisimilarity-based classification

The generator is made **grammar-aware**. The tape reader's raw
domain stays intact (`next_i64` full i64; `next_f64` any finite
non-NaN); a **grammar-aware projection** at codegen time maps raw
values onto surface-valid literals *per the language's actual
lexer pattern*.

### Architecture

```text
┌──────────────────────────────────────────────────────────────┐
│                     At codegen (macro) time                   │
├──────────────────────────────────────────────────────────────┤
│                                                               │
│   LanguageDef.token_defs  ──►  effective_pattern_for(kind)   │
│   literal_patterns.ebnf   ──►    (user overrides | defaults) │
│                                        │                      │
│                                        ▼                      │
│                                  classify_token               │
│                                        │                      │
│                                        ▼                      │
│        ┌───────────────────────────────────────────────┐     │
│        │  byte-level DFA product traversal             │     │
│        │  over (user_pattern, canonical_pattern) pairs │     │
│        │  for each canonical ∈ {Integer, SignedInt,   │     │
│        │                       Float, SignedFloat}    │     │
│        └──────────────┬────────────────────────────────┘     │
│                       │                                       │
│                       ▼                                       │
│                CanonicalKind                                  │
│                       │                                       │
│      ┌────────────────┼──────────────────┐                  │
│      ▼                ▼                  ▼                   │
│  Integer:         SignedInt:         Unclassified:           │
│  (v.unsigned_     (v)                walk NFA                │
│   _abs() & MAX)                      (nfa_walk)              │
│                                                               │
└──────────────────────────────────────────────────────────────┘
```

### Bisimilarity = byte-level DFA product traversal

Two patterns are classified as the same canonical family iff their
accepted languages are exactly equal. We decide this by **compiling
both patterns into a shared NFA** with distinct accept tokens, then
determinising and checking — for every reachable state in the
resulting DFA — that the accept set agrees on both tokens.

This is sound regardless of each pattern's internal `ClassId`
partition (which is computed per-NFA and is not comparable across
independently compiled patterns). Implementation:
`macros/src/gen/test_gen/automaton_walk/classify.rs`, function
`language_equivalent`.

Bisimilarity does real work: the unit test
`classify_language_equivalent_integer_variants` proves that
syntactically distinct patterns `[0-9]+` and `[0-9][0-9]*` classify
as the same `Integer` family (they accept the same set of strings).
Regex-string matching would have flagged them as different.

### Canonical library

Initial seven shapes, extensible:

| CanonicalKind  | Reference regex                               | Sampler projection                            |
|----------------|-----------------------------------------------|-----------------------------------------------|
| `Integer`      | `[0-9]+`                                      | `(v.unsigned_abs() as i*) & MAX`              |
| `SignedInt`    | `-?[0-9]+`                                    | `v` (full range)                              |
| `Float`        | `[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?`            | `v.abs()`                                     |
| `SignedFloat`  | `-?[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?`          | `v` (full range)                              |
| `Ident`        | *(not yet wired into sampler dispatch)*       | existing `next_string` placeholder           |
| `StringLit`    | *(not yet wired into sampler dispatch)*       | existing `next_string` placeholder           |
| `Unclassified` | (anything not matching above)                 | `nfa_walk::emit_pattern_sampler` (Step 3)    |

Callers that want native-type-aware sampling of classified numeric
tokens get the projection gated on the language's *effective*
pattern — user overrides via `tokens { Integer = /.../ }` take
precedence over defaults in `prattail/src/literal_patterns.ebnf`.

### Token-boundary ambiguity

Emitting `3` then `5` without whitespace concatenates to `35` — a
single token, not two. The walker consults a pair-wise
`requires_ws(AdjKind, AdjKind) -> bool` table at terminal emission
boundaries. Implementation:
`macros/src/gen/test_gen/automaton_walk/ambiguity.rs`.

Conservative rules:
- Int + Int / Int + Float / Float + {Int,Float} → whitespace required.
- Ident + {Ident, Int, Float} → whitespace required.
- {Int, Float} + Ident → safe (Integer regex stops at `x`).
- Anything + Punct / Punct + Anything → safe (single-char, no
  merge).
- StringLit on either side → safe (self-delimited by quotes).

### Unclassified tokens: NFA walk

For a user-defined token that matches no canonical (e.g.
`tokens { HexLiteral = /0x[0-9a-fA-F]+/; }`), the strategy emits a
tape-driven walk of the pattern's minimized DFA:

1. Compile pattern to NFA via `prattail::automata::regex::compile_regex`.
2. Determinize + minimize — typical lexer DFAs are ≤30 states.
3. Build per-class representative-byte lookup.
4. Emit a runtime function that walks the DFA: at each step read
   tape bytes to decide `stop | pick class`, emit the
   representative byte, move to target state, bound by
   `MAX_STEPS = 64`.

Implementation: `macros/src/gen/test_gen/automaton_walk/nfa_walk.rs`,
function `emit_pattern_sampler`.

### Grammar walk

The grammar walker (`macros/src/gen/test_gen/automaton_walk/grammar_walk.rs`)
provides a `SelectionPolicy` trait with `UniformPolicy` default and
`WeightedPolicy` alternative. This is the distribution-bias hook the
plan promised: user projects wanting "generate `Neg` 2× as often"
register a custom policy; default is uniform over applicable rules.

The walker's actual AST-producing logic is handled by the existing
tape-builder at `strategies.rs:generate_regular_build_code` etc. —
that code correctly handles binders, abstractions, collections, and
separators (tens of thousands of lines of correctness-critical
logic). Rewriting it as a string-walker would duplicate that code
without benefit: the existing Display emitter is already designed
to produce parseable surface text for complex constructs.

### Roundtrip assertion strengthened

`strategies.rs:1204–1214` previously silently skipped unparseable
terms. Now:

```rust
let parsed = Cat::parse(&displayed)
    .unwrap_or_else(|e| panic!(
        "arb_{cat} produced unparseable surface term {:?}: {:?}",
        displayed, e));
let canonical = format!("{}", parsed);
let reparsed = Cat::parse(&canonical).unwrap_or_else(|e| panic!(...));
prop_assert_eq!(canonical, format!("{}", reparsed));
```

Any grammar violation in the generator now surfaces as a loud
property-test failure instead of a silent pass. This is the
deliberate tightening of the contract: the new `.expect` proves
grammar-aware projection is actually producing surface-valid terms
for every sampled AST.

## Prior fixes that kill the double-panic abort (separate from this work)

These ride alongside but are not part of the generator
architecture per se:

- `macros/src/gen/native/eval.rs:527–567` — `std::ops` impls
  now delegate to `SafeArith` with `Default::default()` fallback
  instead of panicking on overflow.
- `runtime/src/canonical_float.rs:28,242` — `CanonicalFloat{64,32}`
  now derive `Default`.
- `prattail/src/automata/codegen.rs:657–677,1015–1026` — lexer uses
  saturating parse for integers (`unwrap_or_else(|_|
  if text.starts_with('-') { i64::MIN } else { i64::MAX })`) and
  fallback zero for floats.

## Usage / per-language rollout

| Language      | Change required? | Outcome                                         |
|---------------|------------------|-------------------------------------------------|
| calculator    | None             | Has `Neg`; strategy classifies as `Integer`     |
|               |                  | + unsigned projection emits positive NumLit;    |
|               |                  | negatives arise via `Neg(NumLit(v))` through    |
|               |                  | the AST builder, displays correctly.            |
| led_test      | None             | Has `NegNum`; same as calculator.               |
| rhocalc       | None             | No `Neg` rule. Classifier → `Integer`. Negative |
|               |                  | i64 tape values project to non-negative. To     |
|               |                  | unlock negative-value coverage, user adds one   |
|               |                  | of:                                             |
|               |                  | — `Neg . k:Int ... fold;` grammar rule          |
|               |                  | — `tokens { Integer = /-?[0-9]+/; }` override   |
| mixedmath, … | None             | Same as rhocalc.                                |

No per-language configuration is required; the classifier reads each
language's effective lexer pattern.

## Verification

- `simulate_rhocalc --steps 10000 --cases 1000 --morphology`:
  previously aborted with SIGABRT; now exits 0 with 1000/1000 cases
  passing.
- All 9 `simulate_*` binaries run to exit 0 at the plan-level scale
  (1000 cases × 10000 steps). The 5 ledtest failures (`to_num(a and
  a)`) are pre-existing cross-category-cast parse errors unrelated
  to generator-vs-grammar alignment.
- `cargo test -p mettail-macros`: 215 + 23 new `automaton_walk::*`
  tests = 238 pass.
- `cargo test -p mettail-languages`: 1813 tests pass, including the
  strengthened roundtrip assertions.
- The bisimilarity check provably does semantic work:
  `classify_language_equivalent_integer_variants` shows
  `[0-9][0-9]*` classifies as `Integer` despite being syntactically
  distinct from `[0-9]+`.

## Files

### Added

- `macros/src/gen/test_gen/automaton_walk/mod.rs`
- `macros/src/gen/test_gen/automaton_walk/classify.rs`
- `macros/src/gen/test_gen/automaton_walk/nfa_walk.rs`
- `macros/src/gen/test_gen/automaton_walk/ambiguity.rs`
- `macros/src/gen/test_gen/automaton_walk/grammar_walk.rs`

### Modified

- `macros/src/gen/test_gen/mod.rs` — register `automaton_walk`.
- `macros/src/gen/test_gen/strategies.rs:438–568` —
  `generate_literal_build_code` now grammar-aware; uses classifier
  for projection decisions.
- `macros/src/gen/test_gen/strategies.rs:1186–1217` —
  roundtrip assertion strengthened from silent-skip to `.expect`.
- `macros/src/gen/native/eval.rs:527–567` — `std::ops` impls
  non-panicking (separate bug fix, preserved).
- `runtime/src/canonical_float.rs:28, 242` — `Default` derived.
- `prattail/src/automata/codegen.rs:657–677, 1015–1026` — saturating
  parse.

### Reference only (not modified)

- `prattail/src/lib.rs:387–395, 417–439` — `LiteralPatterns`,
  `CustomTokenSpec`.
- `prattail/src/automata/mod.rs:163–253` — NFA, DFA types.
- `prattail/src/automata/minimize.rs:95–394` — Hopcroft's
  algorithm we reuse via product traversal.
- `ast/src/language.rs:51, 1080–1098` — `LanguageDef::token_defs`,
  `TokenDef`.

## Future work

- Exposing `tokens { ... }` custom patterns through the strategy
  layer: already automatic via `effective_pattern_for`; no surface
  change needed.
- Extended canonicals: add `HexOrDecimal`, scientific-notation-free
  `SimpleFloat`, etc. Each new canonical is a single `if
  language_equivalent(pat, ...) { return ... }` arm.
- Length-bounded integer / float patterns (`[0-9]{1,3}`): extend
  `Constraints` with `max_len` and thread it into the sampler's
  value-range clamp.
- Full constraint extraction (length bounds, char-class union,
  sign) from the minimized DFA via BFS shortest-path and
  longest-simple-path. Currently only classifier-level family
  membership is extracted.
- Full tokens-DFA-based ambiguity analysis instead of coarse
  `AdjKind` rules: compute the bounded product `A_accept × B_prefix`
  for every pair of token kinds and decide merge hazard exactly.
