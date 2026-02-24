# PraTTaIL vs LALRPOP Parse Performance

## Summary

PraTTaIL achieves **21x to 900x speedup** over LALRPOP for parse-only benchmarks across
all 4 languages (Ambient, Calculator, Lambda, RhoCalc). The geometric mean speedup
across all 39 benchmarks is approximately **192x**.

**Date:** 2026-02-14 (updated 2026-02-16)
**Branch:** `feature/improved-parsing`
**Benchmark harness:** Criterion 0.5
**Build profile:** `bench` (optimized, `opt-level = 3`)
**Benchmark source:** `languages/benches/parse_bench.rs`

**Note:** These benchmarks were measured during Phase 2 (before LALRPOP removal in Phase 3)
using the original `parse_bench.rs` which benchmarked both backends. Given the magnitude of
the speedups (17-893x), the relative ordering is unambiguous regardless of scheduling noise.
For production benchmarking, CPU affinity (`taskset -c 0`) and performance governor should be
used for stable measurements. Hardware specifications for these benchmarks are documented in
`~/.claude/hardware-specifications.md`.

**Status:** Since Phase 3 (LALRPOP removal), these benchmarks serve as a historical reference
documenting the performance comparison that justified the migration from LALRPOP to PraTTaIL.
PraTTaIL has since been further optimized with zero-copy lexing (Sprint 5E) and Aho-Corasick
keyword trie NFA (Sprint 5D), which improve both parse-time and codegen-time performance
respectively.

## How to Reproduce

These benchmarks were originally run during Phase 2 when both backends coexisted:

```bash
# Phase 2 commands (historical — LALRPOP has been removed since Phase 3):
# LALRPOP baseline:  cargo bench -p mettail-languages --bench parse_bench
# PraTTaIL:          cargo bench -p mettail-languages --bench parse_bench --features prattail

# Current (Phase 3+, PraTTaIL only):
taskset -c 0 cargo bench -p mettail-languages --bench parse_bench
```

## Results

### Ambient Calculus

| Input | LALRPOP | PraTTaIL | Speedup |
|-------|---------|----------|---------|
| `{}` (zero) | ~83 µs | 218 ns | **380x** |
| `x` (variable) | ~84 µs | 247 ns | **341x** |
| `n[p]` (simple_amb) | ~89 µs | 636 ns | **139x** |
| `in(n,p)` (capability_in) | ~89 µs | 684 ns | **129x** |
| `{p \| q}` (parallel) | ~91 µs | 707 ns | **129x** |
| `n[{in(m,p)}]` (nested) | ~96 µs | 1.19 µs | **80x** |
| `{n[{in(m,p)}] \| m[r]}` (complex) | ~103 µs | 2.46 µs | **41x** |
| `new(x,p)` (new) | ~93 µs | 734 ns | **125x** |
| deep_nested (5 constructs) | ~117 µs | 6.75 µs | **17x** |
| multi_parallel (3 branches) | ~110 µs | 3.79 µs | **29x** |

### Calculator

| Input | LALRPOP | PraTTaIL | Speedup |
|-------|---------|----------|---------|
| `42` (integer) | ~113 µs | 126 ns | **893x** |
| `x` (variable) | ~108 µs | 240 ns | **449x** |
| `1 + 2` (addition) | ~114 µs | 217 ns | **526x** |
| `1 + 2 + 3` (chain_add) | ~113 µs | 430 ns | **262x** |
| `1 + 2 - 3` (mixed_ops) | ~116 µs | 400 ns | **287x** |
| `2 ^ 3` (power) | ~116 µs | 215 ns | **535x** |
| `true` (bool_true) | ~227 µs | 648 ns | **347x** |
| `false` (bool_false) | ~227 µs | 677 ns | **337x** |
| `"hello"` (string_lit) | ~341 µs | 1.26 µs | **270x** |
| `"a" ++ "b"` (string_concat) | ~357 µs | 1.58 µs | **224x** |
| `1 + 2 + 3 + 4 + 5` (complex_expr) | ~114 µs | 703 ns | **161x** |

### Lambda Calculus

| Input | LALRPOP | PraTTaIL | Speedup |
|-------|---------|----------|---------|
| `x` (variable) | ~71 µs | 275 ns | **259x** |
| `lam x.x` (abstraction) | ~76 µs | 678 ns | **111x** |
| `(x,y)` (application) | ~74 µs | 586 ns | **127x** |
| `lam x.lam y.x` (nested_lam) | ~77 µs | 1.04 µs | **74x** |
| Y-combinator (complex) | ~86 µs | 3.44 µs | **25x** |

### RhoCalc (Rho Calculus)

| Input | LALRPOP | PraTTaIL | Speedup |
|-------|---------|----------|---------|
| `{}` (zero) | ~87 µs | 114 ns | **769x** |
| `x` (variable) | ~96 µs | 241 ns | **398x** |
| `42` (integer) | ~92 µs | 141 ns | **654x** |
| `error` | ~95 µs | 183 ns | **518x** |
| `*(n)` (drop) | ~99 µs | 448 ns | **220x** |
| `@(p)` (quote) | ~197 µs | 1.08 µs | **180x** |
| `x!(p)` (output) | ~97 µs | 619 ns | **156x** |
| `1 + 2` (addition) | ~101 µs | 246 ns | **411x** |
| `{p \| q}` (parallel) | ~101 µs | 683 ns | **147x** |
| `*(@(p))` (drop_quote) | ~100 µs | 506 ns | **195x** |
| `{x!(p) \| y!(q)}` (nested_output) | ~110 µs | 1.36 µs | **80x** |
| `(x?a, y?b).{*(a)}` (multi_input) | ~111 µs | 2.11 µs | **52x** |
| complex (4 processes) | ~126 µs | 3.94 µs | **32x** |

## Analysis

### Why PraTTaIL is Faster

1. **No table-driven LR(1) overhead.** LALRPOP generates a table-driven parser that
   performs state transitions via table lookups at runtime. PraTTaIL generates direct
   function calls — the parse decisions are compiled into native branch instructions.

2. **Minimal allocation.** PraTTaIL's generated lexer produces a flat `Vec<(Token, Span)>`
   in a single pass. LALRPOP's `lalrpop-util` lexer creates iterator-based token streams
   with per-token Result wrapping.

3. **Pratt parsing is inherently cache-friendly.** The Pratt loop is a tight `loop { match }`
   on token binding powers — no indirect jumps through state tables.

4. **No grammar-conflict workaround overhead.** LALRPOP requires tiered productions
   (`Cat`/`CatInfix`/`CatAtom`) to encode precedence, which adds extra reduction steps.
   PraTTaIL encodes precedence directly in binding power comparisons.

### Scaling Pattern

Speedup decreases with input complexity:
- **Simple atoms** (zero, integer, variable): 340-893x
- **Medium expressions** (infix, output, drop): 130-535x
- **Complex nested terms** (deep nesting, multi-input): 17-80x

This is expected: for trivial inputs, LALRPOP's fixed per-parse overhead (~85-110 µs)
dominates, while PraTTaIL's overhead is near-zero (~100-250 ns). As input complexity
grows, actual parsing work becomes the dominant factor, and the speedup converges toward
the "true" algorithmic advantage (~15-30x for complex inputs).

### Absolute Performance

PraTTaIL achieves sub-microsecond parse times for simple expressions and stays under
7 µs even for deeply nested 40+ character inputs. This is fast enough for:
- Interactive REPL use (imperceptible latency)
- Batch processing of thousands of terms per second
- Embedding as a hot path in evaluation loops

## Generated Code Size Comparison

PraTTaIL generates significantly less code than LALRPOP. Measured across all 4 languages
(Ambient, Calculator, Lambda, RhoCalc):

| Metric | LALRPOP (main branch) | PraTTaIL (feature/improved-parsing) | Change |
|--------|----------------------|-------------------------------------|--------|
| **Total generated lines** | ~15,000–20,000+ per language | ~1,500–2,000 per language | **~90% reduction** |

The reduction comes from several factors:

1. **Direct-coded lexer vs regex-based.** PraTTaIL generates a DFA-based lexer as compact
   match arms. LALRPOP relies on `lalrpop-util`'s regex-based lexer with large generated tables.

2. **Pratt parser vs LR(1) tables.** Pratt parsing encodes precedence in ~8 lines of binding
   power functions instead of thousands of lines of LR(1) state transition tables.

3. **String-based codegen.** PraTTaIL builds the entire parser as a single `String` buffer,
   parsed once to `TokenStream`. This avoids the overhead of `quote!` macro expansion and
   produces more compact output than LALRPOP's code generation approach.

4. **No tiered productions.** LALRPOP requires `Cat`/`CatInfix`/`CatAtom` tiers to encode
   precedence, tripling the number of production rules. PraTTaIL handles this with numeric
   binding powers in a single Pratt loop.

## Post-Optimization Improvements (Phase 3+)

Since the Phase 2 benchmarks above, PraTTaIL has undergone several further optimizations
that improve both parse-time and codegen-time performance:

| Optimization | Sprint | Impact |
|-------------|--------|--------|
| String-based codegen (lexer) | Phase 2, Exp 6 | Codegen: **-23% to -29%** |
| String-based codegen (parser) | Sprint 5B | Per-component: **-90% to -98%** |
| Pipeline architecture | Sprint 5C | End-to-end: **-1.5% to -7.3%** |
| Aho-Corasick keyword trie | Sprint 5D | NFA state reduction: **~30–42%** |
| Zero-copy lexing | Sprint 5E | Zero `String` allocs during lex |
| Panic-mode error recovery | Sprint 4A | Functional addition (zero overhead on non-recovering path) |
| DAFSA suffix sharing | Sprint 5F | NFA sharing for large grammars (no impact on current 4 grammars) |
| Comb/bitmap compression | Sprint 5F | Table compression for >30-state DFAs (not triggered by current grammars) |
| BFS canonical state ordering | Performance investigation | Deterministic DFA state numbering; geomean **173x → 192x** |

The zero-copy lexing improvement (Sprint 5E) is the most impactful for parse-time performance:
`Token<'a>` borrows `&'a str` directly from the input for `Ident`, `StringLit`, `Dollar`, and
`DoubleDollar` variants, eliminating per-token `String` allocations during lexing. String
allocation is deferred to AST construction (`.to_string()` at `get_or_create_var` call sites).

For detailed codegen pipeline optimization data, see the
[Optimization Ledger](optimization-ledger.md).
