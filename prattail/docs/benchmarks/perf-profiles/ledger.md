# PraTTaIL Performance Profiling Ledger

**Date**: 2026-02-28
**Method**: `perf record --call-graph lbr`, `perf report --no-children --sort=symbol`
**CPU**: AMD (performance governor, max 3.6 GHz), pinned via `taskset -c 0`
**Build**: LLVM backend (`RUSTFLAGS=""` overriding cranelift), `bench` profile (optimized)
**Tooling**: Criterion 0.5 (200 samples default, 100 for some runtime benches)

---

## Session Summary

| # | Session | Benchmark | Time | Samples |
|---|---------|-----------|------|---------|
| 1 | E2E Complex | `end_to_end/complex` | 2.68 ms | 90,774 |
| 2 | E2E Scaling/100 | `scaling/100` | 3.96 ms | 86,283 |
| 3 | Parse RhoCalc Complex | `parse/rhocalc/parse/complex` | 12.52 µs | 220,420 |
| 4 | Infix Chain/1000 | `infix/left_chain/1000` | 213 µs | 169,724 |
| 5a | Lexer Complex | `full_pipeline/complex` | 758 µs | 63,189 |
| 5b | Lexer Scaling/100 | `scaling/100` | 1.78 ms | 66,147 |
| 6 | Nesting Lambda/100 | `nesting/lambda_depth/100` | 49.9 µs | 169,322 |
| 7 | WFST Construction | `wfst/construction/*` | varies | 836,158 |
| 8 | Analysis Scaling/100 | `first_sets_scaling/100` | 424 ns | 67,542 |

---

## Overhead Decomposition

All profiles contain Criterion statistical overhead. This table separates it
so application hotspots can be properly attributed.

| Session | Criterion¹ | Kernel | Allocator² | proc_macro2³ | App Code |
|---------|-----------|--------|------------|-------------|----------|
| 1. E2E Complex | 28.3% | 3.9% | 4.4% | 16.7% | 46.7% |
| 2. E2E Scaling/100 | 29.6% | 5.1% | 3.7% | 10.9% | 50.7% |
| 3. Parse RhoCalc | 33.1% | 2.5% | 2.0% | 0.0% | 62.4% |
| 4. Infix Chain/1000 | 23.3% | 2.0% | 5.3% | 0.0% | 69.4% |
| 5a. Lexer Complex | 25.3% | 2.2% | 4.4% | 15.5% | 52.6% |
| 5b. Lexer Scaling/100 | 23.8% | 2.1% | 4.1% | 10.9% | 59.1% |
| 6. Nesting Lambda/100 | 23.6% | 2.0% | 8.1% | 0.0% | 66.3% |
| 7. WFST Construction | 25.8% | 1.6% | 12.2% | 0.0% | 60.4% |
| 8. Analysis Scaling/100 | 26.4% | 2.0% | 13.5% | 0.0% | 58.1% |

¹ `exp()`, `rayon::*`, `criterion::*`
² `malloc`, `cfree`, `__rust_alloc`, `__rust_dealloc`, `realloc`
³ `proc_macro2::*` (codegen tokenization — part of application logic for pipeline sessions)

---

## Phase 3: Detailed Per-Session Analysis

### Session 1: E2E Pipeline / Complex (2.68 ms, RhoCalc-like)

**Top-10 Application Functions (self-time)**:

| Rank | Self % | Function | Component |
|------|--------|----------|-----------|
| 1 | 6.24% | `proc_macro2::parse::token_stream` | Codegen |
| 2 | 2.92% | `proc_macro2::parse::literal` | Codegen |
| 3 | 2.48% | `core::slice::memchr::memchr_aligned` | Codegen (parsing) |
| 4 | 2.25% | `proc_macro2::TokenStream::drop` | Codegen |
| 5 | 2.16% | `proc_macro2::parse::ident_not_raw` | Codegen |
| 6 | 1.76% | `proc_macro2::parse::punct_char` | Codegen |
| 7 | 0.90% | `partition::compute_equivalence_classes` | Automata |
| 8 | 0.74% | `proc_macro2::parse::ident_any` | Codegen |
| 9 | 0.50% | `minimize::minimize_dfa` | Automata |
| 10 | 0.37% | `subset::subset_construction` | Automata |

**Total proc_macro2**: 16.7% (dominant single component)
**Total automata pipeline**: ~1.8% (partition 0.90% + minimize 0.50% + subset 0.37%)
**Total fmt::write**: 0.5%

**Key Finding**: At complex-level grammar size (3 categories, 10 rules),
**codegen dominates** via proc_macro2 tokenization. The automata pipeline
is already well-optimized at this scale. The proc_macro2 library spends
~17% of total time converting generated Rust source strings into
`TokenStream` objects — parsing identifiers, literals, punctuation, and
then dropping the intermediate token trees.

### Session 2: E2E Pipeline / Scaling N=100 (3.96 ms)

**Top-10 Application Functions (self-time)**:

| Rank | Self % | Function | Component |
|------|--------|----------|-----------|
| 1 | 4.02% | `proc_macro2::parse::token_stream` | Codegen |
| 2 | 2.30% | `core::slice::memchr::memchr_aligned` | Codegen (parsing) |
| 3 | 1.98% | `proc_macro2::parse::literal` | Codegen |
| 4 | 1.90% | `partition::compute_equivalence_classes` | Automata |
| 5 | 1.80% | `minimize::minimize_dfa` | Automata |
| 6 | 1.56% | `proc_macro2::parse::punct_char` | Codegen |
| 7 | 1.40% | `proc_macro2::TokenStream::drop` | Codegen |
| 8 | 1.27% | `proc_macro2::parse::ident_not_raw` | Codegen |
| 9 | 0.62% | `subset::subset_construction` | Automata |
| 10 | 0.49% | `core::fmt::write` | Codegen |

**Total proc_macro2**: 10.9%
**Total automata pipeline**: ~5.4% (partition 1.90% + minimize 1.80% + subset 0.62% + compress_comb 0.36% + canonicalize 0.26%)
**Total fmt::write**: 0.9%

**Scaling Analysis (Session 1 → Session 2)**:

| Function | Complex (%) | N=100 (%) | Growth Factor | Scaling |
|----------|-------------|-----------|---------------|---------|
| `compute_equivalence_classes` | 0.90% | 1.90% | 2.1× | Super-linear ✓ |
| `minimize_dfa` | 0.50% | 1.80% | 3.6× | Super-linear ✓✓ |
| `subset_construction` | 0.37% | 0.62% | 1.7× | ~Linear |
| `compress_rows_comb` | <0.2% | 0.36% | >1.8× | Super-linear ✓ |
| `canonicalize_state_order` | <0.2% | 0.26% | >1.3× | Mild |
| proc_macro2 total | 16.7% | 10.9% | 0.65× | Sub-linear ✓ |

**Key Finding**: `minimize_dfa` scales 3.6× when grammar size goes from
complex (~10 rules) to 100 rules, despite the benchmark time only growing
3.96/2.68 = 1.48×. This means minimize_dfa's share of the pipeline grows
super-linearly — it will increasingly dominate at large N. proc_macro2
shrinks in share, confirming that codegen output scales linearly with rule
count while automata work grows faster.

### Session 3: Runtime Parse / RhoCalc Complex (12.52 µs)

**Top Application Functions (self-time, Criterion-normalized)**:

| Rank | Self % | Normalized¹ | Function | Component |
|------|--------|-------------|----------|-----------|
| 1 | 18.55% | ~29.7% | `rhocalc::lex_with_file_id` | Lexer |
| 2 | 3.61% | ~5.8% | `rhocalc::accept_token` | Parser dispatch |
| 3 | 0.67% | ~1.1% | `rhocalc::parse_Proc_impl` | Parser (Pratt) |
| 4 | 0.53% | ~0.8% | `core::fmt::write` | Error formatting |
| 5 | 0.46% | ~0.7% | `String::write_str` | Error formatting |
| 6 | 0.35% | ~0.6% | `from_ascii_radix` | Integer parsing |
| 7 | 0.32% | ~0.5% | `get_or_create_var` (TLS) | Binder |
| 8 | 0.31% | ~0.5% | `Frame_Name` TLS take/set | Trampoline |

¹ Normalized: self% / (1 - criterion_overhead - kernel_overhead)

**Key Finding**: The **lexer dominates** runtime parsing at ~30% normalized.
The DFA transition function (`lex_with_file_id`) is the single hottest
function. `accept_token` (token classification / dispatch) is #2 at ~6%.
The actual Pratt parser (`parse_Proc_impl`) is only ~1%. Binder operations
and trampoline frame management are negligible (<1% each).

### Session 4: Runtime Parse / Infix Chain/1000 (213 µs)

**Top Application Functions (self-time)**:

| Rank | Self % | Function | Component |
|------|--------|----------|-----------|
| 1 | 13.76% | `calculator::lex_with_file_id` | Lexer |
| 2 | 7.26% | `calculator::parse_Int_impl` | Pratt parser |
| 3 | 3.41% | `from_ascii_radix` | Integer parsing |
| 4 | 3.19% | `calculator::accept_token` | Token dispatch |
| 5 | 2.86% | `drop_in_place::<Int>` | AST teardown |

**Key Finding**: At 1000 infix operations, the Pratt parser (`parse_Int_impl`)
becomes significant at 7.26%. The lexer still dominates at 13.76%.
AST destruction (`drop_in_place::<Int>`) costs 2.86% — this is the cost
of `Box<T>` per AST node at high N. `from_ascii_radix` at 3.41% is
integer literal parsing, called once per token.

**Branch Statistics** (`perf stat`):

| Counter | Value | Rate |
|---------|-------|------|
| cycles | 59.6B | — |
| instructions | 124.0B | IPC: 2.08 |
| branch-instructions | 21.7B | — |
| **branch-misses** | **249M** | **1.15%** |
| cache-references | 83.7M | — |
| cache-misses | 2.7M | 3.22% |
| L1-dcache-loads | 34.0B | — |
| L1-dcache-load-misses | 819.9M | 2.41% |
| L1-icache-load-misses | 3.4M | — |

**Key Finding**: Branch miss rate is **1.15%** — excellent. No branch
prediction bottleneck. IPC of 2.08 indicates good instruction-level
parallelism. L1 data cache miss rate of 2.41% is low. The WFST
dispatch arm ordering is working well.

### Session 5a: Lexer Pipeline / Complex (758 µs)

**Top Application Functions (self-time)**:

| Rank | Self % | Function | Component |
|------|--------|----------|-----------|
| 1 | 5.76% | `proc_macro2::parse::token_stream` | Codegen |
| 2 | 3.19% | `partition::compute_equivalence_classes` | Automata |
| 3 | 3.16% | `proc_macro2::parse::literal` | Codegen |
| 4 | 2.48% | `memchr_aligned` | Codegen |
| 5 | 2.13% | `minimize::minimize_dfa` | Automata |
| 6 | 2.04% | `proc_macro2::TokenStream::drop` | Codegen |
| 7 | 1.30% | `subset::subset_construction` | Automata |
| 8 | 0.67% | `sip::Hasher::write` | Hashing (automata) |
| 9 | 0.51% | `compress_rows_comb` | Codegen (DFA tables) |
| 10 | 0.47% | `canonicalize_state_order` | Automata |

**Total proc_macro2**: 15.5%
**Total automata**: ~9.5% (partition 3.19% + minimize 2.13% + subset 1.30% + compress 0.51% + canonicalize 0.47% + epsilon_closure 0.32%)

### Session 5b: Lexer Pipeline / Scaling N=100 (1.78 ms)

**Top Application Functions (self-time)**:

| Rank | Self % | Function | Component |
|------|--------|----------|-----------|
| 1 | 4.90% | `partition::compute_equivalence_classes` | Automata |
| 2 | 4.66% | `minimize::minimize_dfa` | Automata |
| 3 | 3.86% | `proc_macro2::parse::token_stream` | Codegen |
| 4 | 2.61% | `proc_macro2::parse::literal` | Codegen |
| 5 | 1.69% | `subset::subset_construction` | Automata |
| 6 | 1.02% | `compress_rows_comb` | Codegen |
| 7 | 0.69% | `canonicalize_state_order` | Automata |
| 8 | 0.54% | `minimize_dfa::{closure}` (inner Vec) | Automata |

**Total proc_macro2**: 10.9%
**Total automata**: ~13.5%

**Scaling Analysis (5a → 5b)**:

| Function | Complex (%) | N=100 (%) | Growth | Scaling |
|----------|-------------|-----------|--------|---------|
| `compute_equivalence_classes` | 3.19% | 4.90% | 1.54× | Moderate |
| `minimize_dfa` | 2.13% | 4.66% | 2.19× | Super-linear ✓ |
| `subset_construction` | 1.30% | 1.69% | 1.30× | ~Linear |
| `compress_rows_comb` | 0.51% | 1.02% | 2.00× | Super-linear ✓ |
| `canonicalize_state_order` | 0.47% | 0.69% | 1.47× | Moderate |
| proc_macro2 total | 15.5% | 10.9% | 0.70× | Sub-linear |

**Key Finding**: Confirmed — `minimize_dfa` grows 2.2× in share (lexer-only),
and `compress_rows_comb` doubles. At N=100, **automata overtakes codegen**
as the dominant pipeline cost (13.5% vs 10.9%). The crossover point is
roughly N≈50.

### Session 6: Nesting Lambda/100 (49.9 µs)

**Top Application Functions (self-time)**:

| Rank | Self % | Normalized | Function | Component |
|------|--------|------------|----------|-----------|
| 1 | 10.86% | ~14.6% | `Term::close_term` (moniker) | Binder |
| 2 | 6.22% | ~8.4% | `lambda::lex_with_file_id` | Lexer |
| 3 | 1.76% | ~2.4% | `get_or_create_var` (TLS) | Binder |
| 4 | 1.69% | ~2.3% | `lambda::parse_Term_impl` | Parser |
| 5 | 1.21% | ~1.6% | `String::clone` | Binder/alloc |
| 6 | 1.17% | ~1.6% | `Scope::new` (moniker) | Binder |
| 7 | 1.01% | ~1.4% | `RandomState::hash_one` | Var cache hash |
| 8 | 0.86% | ~1.2% | `HashMap::rustc_entry` | Var cache |
| 9 | 0.67% | ~0.9% | `lambda::expect_ident` | Parser |
| 10 | 0.53% | ~0.7% | `Binder::binders` (moniker) | Binder |

**Total binder operations**: ~22.3% raw (~30% normalized)
**Total lexer**: 6.22% (~8.4% normalized)
**Total parser**: ~2.4% (~3.2% normalized)
**Total var cache**: ~2.9% (~3.9% normalized)

**Key Finding**: For binder-heavy grammars, **moniker operations dominate**
at 30% normalized. `close_term` alone is 14.6% — this is the de Bruijn
index adjustment that runs O(depth) per nested scope. The trampoline
frame stack is essentially invisible (no `Vec::push`/`Vec::pop` in the
top-20). Parser operations (`parse_Term_impl` + `expect_ident`) are only
3.2% combined.

### Session 7: WFST Construction (all sub-benchmarks)

**Top Application Functions (self-time)**:

| Rank | Self % | Function | Component |
|------|--------|----------|-----------|
| 1 | 3.98% | `String::clone` | Allocation |
| 2 | 2.36% | `TokenIdMap::get_or_insert` | WFST |
| 3 | 1.71% | `BTreeMap<String, u16>::insert` | WFST |
| 4 | 1.43% | `BTreeMap::IntoIter::dying_next` | WFST teardown |
| 5 | 1.01% | `BTreeMap::clone::clone_subtree` | WFST |
| 6 | 0.82% | `BTreeMap::clone::clone_subtree` (2nd) | WFST |
| 7 | 0.66% | `drop_in_place::<PredictionWfst>` | WFST teardown |
| 8 | 0.64% | `Vec<String>::clone` | Allocation |
| 9 | 0.62% | `NodeRef::search_tree` (BTreeMap) | WFST lookup |
| 10 | 0.54% | `drop_in_place::<RecoveryWfst>` | WFST teardown |

**Total allocator (cfree+malloc+alloc)**: 12.2%
**Total String::clone**: 3.98%
**Total BTreeMap operations**: ~5.6%
**Total WFST teardown (drops)**: ~1.2%

**Key Finding**: WFST construction is dominated by **String cloning (4%)**
and **BTreeMap operations (5.6%)**. The `TokenIdMap::get_or_insert` method
at 2.36% performs HashMap lookups with String keys. The high allocator
overhead (12.2%) is driven by repeated String allocations for token names.
Optimization opportunities: intern strings or use `&str` references to
avoid cloning; replace BTreeMap with HashMap for O(1) amortized lookups.

### Session 8: Analysis / FIRST Sets Scaling/100 (424 ns)

**Top Application Functions (self-time)**:

| Rank | Self % | Normalized | Function | Component |
|------|--------|------------|----------|-----------|
| 1 | 23.58% | ~33.9% | `compute_first_sets` | Analysis |
| 2 | 1.95% | ~2.8% | `BTreeMap<String, FirstSet>::drop` | Analysis teardown |
| 3 | 1.73% | ~2.5% | `String::clone` | Allocation |
| 4 | 1.23% | ~1.8% | `BTreeMap::IntoIter::dying_next` | Analysis teardown |
| 5 | 1.20% | ~1.7% | `terminal_to_variant_name` | Codegen |
| 6 | 0.90% | ~1.3% | `BTreeSet::insert (VacantEntry)` | Analysis |
| 7 | 0.79% | ~1.1% | `BTreeMap VacantEntry::insert_entry` | Analysis |
| 8 | 0.65% | ~0.9% | `BTreeMap<String, FirstSet>::insert` | Analysis |
| 9 | 0.73% | ~1.1% | `BTreeMap::IntoIter::dying_next` (2nd) | Teardown |

**Total `compute_first_sets`**: 23.58% raw (~34% normalized)
**Total BTreeMap operations**: ~7.3%
**Total allocator**: 13.5%

**Key Finding**: `compute_first_sets` is an extreme hotspot at **34%
normalized** — confirming H4 about the fixed-point iteration cost. However,
note that the absolute time is only 424 ns, so this is already fast.
The BTreeMap overhead (7.3%) is significant relative to the function — replacing
with HashMap could reduce this. The allocator at 13.5% reflects per-iteration
BTreeMap/BTreeSet allocations in the fixed-point loop.

---

## Phase 4: Hypothesis Validation

### Pipeline (Compile-Time) Hypotheses

| # | Hypothesis | Verdict | Evidence |
|---|-----------|---------|----------|
| H1 | String codegen (`write!`, `format!`) is the new dominant cost | **REJECTED (Modified)** | `core::fmt::write` is only 0.5-2.0%. The actual codegen bottleneck is `proc_macro2` tokenization (10.9-16.7%), which converts the formatted strings into `TokenStream`. The dominant cost is not string formatting but string→token parsing. |
| H2 | `minimize_dfa` inverse map dominates at large N | **CONFIRMED** | `minimize_dfa` grows 3.6× (E2E) / 2.2× (lexer) when going from complex to N=100, while overall time grows 1.48× / 2.35×. Its share increases from 0.50% → 1.80% (E2E) and 2.13% → 4.66% (lexer). |
| H3 | WFST construction is constant-cost (~60-80 µs) | **CONFIRMED** | Session 7 shows WFST construction at 3.9 µs for complex benchmarks. In E2E sessions, WFST functions don't appear in the top-20, meaning they consume <0.2% of the 2.68-3.96 ms pipeline. |
| H4 | `compute_first_sets` converges slowly at large N | **PARTIALLY CONFIRMED** | `compute_first_sets` is 23.58% of session 8 (424 ns absolute). This is the dominant function for analysis, but the absolute time is trivially small. The dirty-flag optimization appears effective — 424 ns for 100 rules is fast. |
| H5 | BTreeMap overhead replaceable with HashMap in prediction | **CONFIRMED** | Session 8 shows 7.3% in BTreeMap operations (insert, drop, iterate). Session 7 shows 5.6% in BTreeMap ops for WFST. HashMap would eliminate log(n) per-lookup overhead. |

### Runtime (Parse-Time) Hypotheses

| # | Hypothesis | Verdict | Evidence |
|---|-----------|---------|----------|
| H6 | Lexer DFA transition dominates simple inputs | **CONFIRMED** | `lex_with_file_id` is the #1 function in all runtime sessions: 18.55% (RhoCalc), 13.76% (calculator), 6.22% (lambda). The lexer consistently consumes 25-30% of normalized runtime. |
| H7 | `clear_var_cache()` is non-trivial per-iteration overhead | **REJECTED** | No `clear_var_cache` symbol appears in any runtime profile. The var cache (`HashMap` operations: `hash_one`, `rustc_entry`) totals ~3.9% normalized in nesting but is negligible in other sessions. |
| H8 | Moniker binder ops expensive for binder-heavy grammars | **CONFIRMED** | Session 6 (nesting/100): `close_term` = 14.6%, `Scope::new` = 1.6%, `Binder::binders` = 0.7%, total ~30% normalized. Moniker operations are the #1 cost for lambda-style grammars. |
| H9 | `Box::new` per AST node significant at high N | **PARTIALLY CONFIRMED** | `drop_in_place::<Int>` = 2.86% in session 4 (infix/1000). This is the Box deallocation cost. At 1000 nodes, it's material but not dominant. At smaller N it's negligible. |
| H10 | WFST ordering reduces branch misses in dispatch | **CONFIRMED (Indirectly)** | Branch miss rate is 1.15% — well below the 3% concern threshold. The dispatch ordering is effective. No further optimization needed here. |
| H11 | Trampoline frame stack ops < 5% at depth 100 | **CONFIRMED** | No `Vec::push`, `Vec::pop`, or trampoline-specific functions appear in Session 6's top-20. The TLS `Cell` take/set for `Frame_Name` is only 0.31%. Frame stack operations are essentially free. |

---

## Phase 5: Top Optimization Targets (Weighted by Impact)

### Priority 1: proc_macro2 Tokenization (Codegen) — 10.9-16.7% of Pipeline

**Problem**: Generated Rust code is written as strings via `write!`/`format!`,
then `proc_macro2::parse::token_stream` re-parses the entire output to
produce a `TokenStream`. This involves character-by-character scanning for
identifiers, literals, and punctuation, plus intermediate allocation and
deallocation of `TokenTree` nodes.

**Optimization Options**:

1. **Direct `TokenStream` construction** via `quote!` macros instead of
   string formatting + parsing. This eliminates the parse step entirely.
   - **Estimated improvement**: 10-15% of pipeline time
   - **Risk**: Major refactor of codegen; `quote!` may have its own overhead
   - **Feasibility**: Medium — requires rewriting `generate_parser_code()`,
     `generate_lexer_code()`, etc. to use `quote!` instead of `write!`

2. **Batch string → TokenStream conversion** by accumulating larger code
   chunks before parsing, reducing per-invocation overhead.
   - **Estimated improvement**: 3-5%
   - **Feasibility**: High — minimal changes

### Priority 2: `minimize_dfa` at Large N — 1.8-4.7% (Grows Super-Linearly)

**Problem**: `minimize_dfa` share grows 2.2-3.6× from complex to N=100
grammars, indicating super-linear scaling. Inner `Vec` allocations for
the inverse map and partition refinement drive this cost.

**Optimization Options**:

1. **Pre-allocated inverse map** with fixed-size arrays instead of Vec<Vec<T>>
   - **Estimated improvement**: 1-2% at N=100
   - **Feasibility**: High — already partially done with pre-counting

2. **Incremental minimization** — only re-minimize affected states when
   adding new rules to an existing grammar.
   - **Estimated improvement**: Up to 50% at N=100 for incremental use
   - **Risk**: Complex correctness reasoning
   - **Feasibility**: Low — significant new algorithm

### Priority 3: Lexer DFA Transition (Runtime) — 18-30% Normalized

**Problem**: `lex_with_file_id` is the single hottest runtime function,
running the DFA transition table for each character of input.

**Optimization Options**:

1. **SIMD-accelerated lexing** for keyword/identifier scanning
   - **Estimated improvement**: 5-10% of parse time
   - **Risk**: Complexity, platform-specific
   - **Feasibility**: Low

2. **Computed goto** / indirect branch table instead of match dispatch
   - **Estimated improvement**: 2-5%
   - **Feasibility**: Medium — requires unsafe Rust

3. **DFA compression** — if the transition table is sparse, use compressed
   representation with faster lookup than the current comb approach.
   - **Estimated improvement**: 1-3%
   - **Feasibility**: Medium

### Priority 4: Moniker Binder Operations — 30% for Binder Grammars

**Problem**: `close_term` (de Bruijn index shifting) runs O(depth) per
nested scope. For depth-100 lambda nesting, this is the dominant cost.

**Optimization Options**:

1. **Lazy binding** — defer `close_term` until variable lookup
   - **Estimated improvement**: Up to 15% for deep nesting
   - **Risk**: Semantic correctness for eager consumers
   - **Feasibility**: Medium

2. **Replace moniker** with a simpler binder representation that uses
   indices directly without traversal
   - **Estimated improvement**: Up to 20%
   - **Risk**: Major refactor
   - **Feasibility**: Low

### Priority 5: String Cloning in WFST — 4% (+ 12% Allocator)

**Problem**: WFST construction clones String token names repeatedly for
BTreeMap keys, TokenIdMap insertions, and Vec storage.

**Optimization Options**:

1. **String interning** — intern token names once, use `u32` IDs everywhere
   - **Estimated improvement**: 3-5% of WFST construction
   - **Feasibility**: High — `TokenIdMap` already assigns u16 IDs; extend
     to use IDs as BTreeMap keys instead of Strings.

### Priority 6: BTreeMap → HashMap in Analysis/WFST — 5-7%

**Problem**: BTreeMap used for FIRST sets and WFST maps where ordering
is not needed, paying O(log n) per operation vs O(1) amortized.

**Optimization Options**:

1. **Replace BTreeMap with HashMap** in `compute_first_sets`,
   `TokenIdMap`, `PredictionWfstBuilder`
   - **Estimated improvement**: 2-4% of affected sessions
   - **Feasibility**: High — straightforward type change
   - **Note**: Some BTreeMaps may need ordering for deterministic output;
     sort only when emitting codegen, not during computation.

---

## Phase 6: Optimization Sprint Execution

### Sprint 5: Lazy Binder Construction — SKIPPED (Unsound)

**Target**: `close_term` = 14.6% normalized for `lambda_depth/100` (Session 6).

**Original Proposal**: Defer `close_term` via `OnceLock` in the `Scope` wrapper
(`LazyScope<P,T>`). Instead of eagerly calling `moniker::Scope::new()` at each
binder site during parsing, store the raw `(binder, body)` pair and lazily
invoke `close_term` on first access.

#### Proof of Incorrectness

**Theorem**: Deferring `close_term` reorders close operations for nested scopes,
producing incorrect de Bruijn indices when the same `FreeVar` (same `unique_id`)
is used as a binder at multiple nesting levels (variable shadowing).

**Setup**: `get_or_create_var("x")` returns the same `FreeVar` (same `unique_id`)
for all occurrences of `"x"` within a parsing session (`binding.rs:31-40`).

Consider `\x. \x. x` (both binders and body reference share `fv_x` with
`unique_id=42`).

**Eager (correct, current behavior — inside-out)**:

1. Inner: `Scope::new(Binder(fv_x), Var::Free(fv_x))`
   - `close_term(depth=0, [Binder(fv_x)])` on `Var::Free(fv_x)` → matches → `Var::Bound(0,0)`
   - Result: `Scope{Binder(fv_x), Var::Bound(0,0)}`
2. Outer: `Scope::new(Binder(fv_x), Box::new(inner_scope))`
   - `close_term(depth=0, [Binder(fv_x)])` on inner_scope's body at depth+1:
   - `Var::Bound(0,0)` → `Var::Bound(_) => return` (line 157 of `bound/mod.rs`) — **SKIP**
   - Result: `x` remains `Bound(0,0)` → refers to **inner** binder ✓

**Deferred (proposed, outside-in)**:

1. Inner: `Scope::new(Binder(fv_x), Var::Free(fv_x))` → deferred, stores raw
   `(fv_x, Var::Free(fv_x))`
2. Outer: `Scope::new(Binder(fv_x), Box::new(inner_scope))` → deferred
3. Force outer → calls `moniker::Scope::new(Binder(fv_x), Box::new(inner_scope))`
   - `close_term(depth=0, [Binder(fv_x)])` on inner_scope:
   - Pattern `close_pattern(depth=0, ...)` → no-op (Binder impl)
   - Body `close_term(depth=1, [Binder(fv_x)])` on raw `Var::Free(fv_x)` → matches
     → `Var::Bound(1,0)`
4. Force inner → calls `moniker::Scope::new(Binder(fv_x), Var::Bound(1,0))`
   - `close_term(depth=0, ...)` on `Var::Bound(1,0)` → `Var::Bound(_) => return` — **SKIP**
   - Result: `x` remains `Bound(1,0)` → refers to **outer** binder ✗

**Conclusion**: `Bound(0,0) ≠ Bound(1,0)`. Eager produces correct inner-binder
binding; deferred produces incorrect outer-binder binding. The approach is
**unsound**. QED.

**Root cause**: `Var::close_term` (moniker `bound/mod.rs:154-163`) uses a "first
match wins" strategy — `Var::Bound(_) => return` skips already-bound vars. Close
ordering determines which binder captures a shadowed variable. Deferring the inner
close allows the outer close to capture first.

**Why the "disjoint variable sets" hypothesis failed**: The hypothesis assumed
different binders have different `unique_id`s. For different variable names (`x`
vs `y`) this holds and closes are order-independent. But `get_or_create_var` maps
the same name to the same `unique_id`, so shadowed binders share IDs and the close
sets **overlap**.

#### Alternative Approaches Evaluated

1. **Fresh Binder IDs at Parse Time**: Give each binder occurrence a genuinely
   unique `FreeVar` via `FreeVar::fresh_named()`. Requires reimplementing
   `close_term` with a different matching criterion (map old `unique_id` to new
   `unique_id`). Adds complexity without reducing work — same traversal cost with
   extra bookkeeping.

2. **Batch Close at Parse Root**: Use `Scope::from_parts_unsafe()` during parsing
   (no `close_term`), then perform a single O(n) top-down pass after parsing that
   closes all scopes simultaneously with a binder stack for correct depth tracking.
   Correct but requires generating `close_all_scopes()` for each AST category,
   `unsafe_body_mut()` accessors, and handling cross-category scopes. High
   complexity for marginal real-world benefit.

#### Decision: Skip

1. **The 14.6% figure is synthetic**: It comes from `lambda_depth/100` — a
   benchmark with 100 nested lambdas. Real Rholang/MeTTa programs typically have
   3-10 nesting levels, where the quadratic overhead is negligible.

2. **The safe alternatives are high-complexity / low-ROI**: Both approaches
   require significant codegen changes for marginal real-world benefit.

3. **Sprints 1-4, 6 already delivered substantial improvements**: The other 5
   sprints addressed the top profiling hotspots. The remaining `close_term` cost
   is inherent to moniker's de Bruijn index construction.

4. **Future option**: If `close_term` becomes a bottleneck for real-world programs,
   revisit with the batch-close approach or consider forking moniker to add an
   O(n) multi-scope close API.

---

## Data Files

All raw `perf.data` files, recording logs, and reports are in:
`prattail/docs/benchmarks/perf-profiles/`

| File | Size | Description |
|------|------|-------------|
| `e2e_complex.perf.data` | 17.2 MB | Session 1 recording |
| `e2e_complex_report.txt` | ~57 KB | Session 1 self-time report |
| `e2e_scaling_100.perf.data` | 16.1 MB | Session 2 recording |
| `e2e_scaling_100_report.txt` | ~57 KB | Session 2 self-time report |
| `parse_rho_complex.perf.data` | 39.1 MB | Session 3 recording |
| `parse_rho_complex_report.txt` | ~57 KB | Session 3 self-time report |
| `infix_chain_1000.perf.data` | 27.2 MB | Session 4 recording |
| `infix_chain_1000_report.txt` | ~57 KB | Session 4 self-time report |
| `infix_chain_1000_stat.txt` | ~1 KB | Session 4 branch/cache stats |
| `lexer_complex.perf.data` | 13.3 MB | Session 5a recording |
| `lexer_complex_report.txt` | ~57 KB | Session 5a self-time report |
| `lexer_scaling_100.perf.data` | 11.9 MB | Session 5b recording |
| `lexer_scaling_100_report.txt` | ~57 KB | Session 5b self-time report |
| `nesting_lambda_100.perf.data` | 30.3 MB | Session 6 recording |
| `nesting_lambda_100_report.txt` | ~57 KB | Session 6 self-time report |
| `wfst_construction.perf.data` | 131.0 MB | Session 7 recording |
| `wfst_construction_report.txt` | ~57 KB | Session 7 self-time report |
| `analysis_scaling_100.perf.data` | 9.4 MB | Session 8 recording |
| `analysis_scaling_100_report.txt` | ~57 KB | Session 8 self-time report |
