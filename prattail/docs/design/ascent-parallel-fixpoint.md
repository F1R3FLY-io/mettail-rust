# Ascent Parallel Fixpoint Design

## 1. Motivation

PraTTaIL generates Datalog programs (via the `ascent` crate) for rewriting, equation matching, and type inference. The `ascent!` macro generates serial (single-threaded) fixpoint evaluation. The `ascent_par!` macro generates parallel (Rayon-based) fixpoint evaluation, which can exploit multi-core CPUs for faster convergence on large grammars.

The goal of this feature is to allow downstream crates to switch between serial and parallel fixpoint evaluation via a cargo feature flag (`ascent-parallel`), without modifying any grammar definitions or rewrite rules.

### Performance Context

For large grammars (e.g., Rholang with 66 rules across 6 categories), the fixpoint evaluation dominates `exec add` latency. Parallel semi-naive evaluation can reduce this by 2-4x on multi-core machines, depending on the number of independent relations and the degree of join parallelism.

## 2. Problem Analysis

### ascent! vs ascent_par!

The `ascent` crate provides two macro families:

| Macro | Iteration | Iterator Type | eqrel Iterator Type |
|-------|-----------|---------------|---------------------|
| `ascent!` | Serial | `&(T, T)` | `&(T, T)` |
| `ascent_par!` | Parallel (Rayon) | `&(T, T)` | `&&(T, T)` |

The critical difference is in **eqrel** (equivalence relation) iterators. In serial mode, `eqrel` relations implement `IndCommon` which yields `&(T, T)` references. In parallel mode, `eqrel` relations implement `CEqRelIndCommon` which yields `&&(T, T)` — an extra level of indirection.

This means code that works with `ascent!` fails to compile with `ascent_par!` when eqrel joins are used, because the pattern destructuring expects `&(a, b)` but receives `&&(a, b)`.

### The Iterator Type Mismatch

Consider this generated rule:

```rust
rw_proc(s1.clone(), t.clone()) <--
    eq_proc(s0, s1),        // eqrel join
    rw_proc(s0, t);         // regular relation join
```

With `ascent!`, `eq_proc(s0, s1)` binds `s0: &Proc` and `s1: &Proc`.

With `ascent_par!`, `eq_proc(s0, s1)` binds `s0: &&Proc` and `s1: &&Proc` — the eqrel's parallel index wraps the reference in an additional `&`.

Calling `s0.clone()` on `&&Proc` gives `&Proc` (cloning the outer reference), not `Proc` (cloning the inner value). This causes type mismatches in subsequent positions.

### Scope of the Problem

Every generated rule that joins on an `eq_*` (eqrel) relation is affected. In Rholang, this includes:

- `rw_proc(s1, t) <-- eq_proc(s0, s1), rw_proc(s0, t)` (rewrite closure)
- `eq_proc(a, b) <-- eq_proc(a, mid), eq_proc(mid, b)` (transitivity)
- All category-specific equation propagation rules

## 3. Solution Design

### F1: Eqrel Clone-Dereference Fix

The fix introduces temporary variables that bind the eqrel iterator outputs and immediately clone-dereference them into the expected types. This works correctly with both `ascent!` and `ascent_par!`:

**Before (breaks with ascent_par!):**
```rust
rw_proc(s1.clone(), t.clone()) <--
    eq_proc(s0, s1),
    rw_proc(s0, t);
```

**After (works with both):**
```rust
rw_proc(__eqrel_closure_a.clone(), c.clone()) <--
    eq_proc(__eqrel_a, __eqrel_b),
    let __eqrel_closure_a = __eqrel_a.clone(),
    let __eqrel_closure_b = __eqrel_b.clone(),
    rw_proc(__eqrel_closure_b, c);
```

The `let __eqrel_closure_a = __eqrel_a.clone()` step:
- With `ascent!`: `__eqrel_a: &Proc`, `.clone()` gives `Proc`. No-op overhead.
- With `ascent_par!`: `__eqrel_a: &&Proc`, `.clone()` gives `&Proc`, then the implicit dereference in the subsequent join position resolves to `Proc`.

The key insight is that `.clone()` on `&&T` returns `&T` (cloning the outer reference), and `.clone()` on `&T` returns `T` (cloning the inner value). By always cloning into a temporary, the code works at both reference levels.

### F2: Feature-Gated Macro Switch

The `generate_ascent_struct()` function in `macros/src/gen/runtime/language.rs` emits a `#[cfg]`-gated pair:

```rust
#[cfg(not(feature = "ascent-parallel"))]
ascent::ascent! {
    struct LanguageName;
    // ... relations and rules ...
}

#[cfg(feature = "ascent-parallel")]
ascent::ascent_par! {
    struct LanguageName;
    // ... relations and rules (identical content) ...
}
```

The `#[cfg(feature = "ascent-parallel")]` attribute is evaluated in the **expansion-site crate** (e.g., `mettail-languages`), not in the proc-macro crate (`mettail-macros`). This allows each downstream crate to independently opt into parallel execution.

### Architecture

```text
language! {                                 Cargo.toml:
    name = "RhoCalc";                       [features]
    Proc { ... }                            ascent-parallel = ["mettail-prattail/ascent-parallel"]
    Name { ... }
}
    │
    ▼ (macro expansion)
┌──────────────────────────────────────────────────────────┐
│ F1: Eqrel clone-dereference fix                          │
│     eq_cat(a, b)  →  let a' = a.clone(), b' = b.clone() │
│     Applied in: macros/src/logic/rules.rs                │
│                 macros/src/logic/mod.rs                   │
└───────────────────────┬──────────────────────────────────┘
                        │
                        ▼
┌──────────────────────────────────────────────────────────┐
│ F2: cfg-gated macro switch                               │
│     #[cfg(not(feature = "ascent-parallel"))]             │
│     ascent! { struct RhoCalc; ... }                      │
│                                                          │
│     #[cfg(feature = "ascent-parallel")]                  │
│     ascent_par! { struct RhoCalc; ... }                  │
│     Applied in: macros/src/gen/runtime/language.rs       │
└──────────────────────────────────────────────────────────┘
                        │
                        ▼
┌──────────────────────────────────────────────────────────┐
│ Generated struct: RhoCalc                                │
│   Serial: single-threaded semi-naive iteration           │
│   Parallel: Rayon par_iter semi-naive iteration          │
└──────────────────────────────────────────────────────────┘
```

## 4. Files Modified

| File | Change |
|------|--------|
| `macros/src/logic/rules.rs` | F1: Eqrel clone-dereference temporaries in rewrite closure rules (`__eqrel_*` variables) |
| `macros/src/logic/mod.rs` | F1: Eqrel clone-dereference in equation propagation rules (lines ~1642-1648) |
| `macros/src/gen/runtime/language.rs` | F2: `generate_ascent_struct()` with `#[cfg]`-gated `ascent!`/`ascent_par!` pair |
| `prattail/Cargo.toml` | Feature declaration: `ascent-parallel = []` |
| `languages/Cargo.toml` | Feature forwarding: `ascent-parallel = ["mettail-prattail/ascent-parallel"]` |

## 5. Feature Gate

### Declaration

In `prattail/Cargo.toml`:

```toml
## Ascent parallel fixpoint: switches ascent! → ascent_par! for parallel rewriting.
ascent-parallel = []
```

In `languages/Cargo.toml`:

```toml
## Ascent parallel fixpoint: switches ascent! → ascent_par! for parallel
## rewriting in generated language structs. Requires F1 eqrel dereference fix.
ascent-parallel = ["mettail-prattail/ascent-parallel"]
```

### Usage

To enable parallel fixpoint evaluation:

```sh
cargo build --features ascent-parallel
cargo test --features ascent-parallel
```

Or in a dependent crate's `Cargo.toml`:

```toml
[dependencies]
mettail-languages = { path = "../languages", features = ["ascent-parallel"] }
```

### Invariant

The `ascent-parallel` feature must not change the **semantics** of the generated program. The fixpoint is the same; only the iteration strategy (serial vs parallel) changes. The F1 fix ensures that the generated rules produce identical results under both strategies.

**Theorem (Semantic Equivalence)**. For any grammar `G` and input `I`, let `R_s` be the fixpoint computed by `ascent!` and `R_p` be the fixpoint computed by `ascent_par!`. Then `R_s = R_p`.

*Proof sketch.* The `ascent` crate's semi-naive evaluation computes the minimal fixpoint of the Datalog program. The parallel variant (`ascent_par!`) uses the same semi-naive algorithm but executes each stratum's delta iteration using Rayon's `par_iter()` instead of `iter()`. Since:

1. Datalog fixpoints are order-independent (the join is commutative and associative).
2. The F1 fix produces identical bound values at both iterator reference levels.
3. Rayon's `par_iter()` computes the same reduction as `iter()` (just in parallel).

The fixpoints are identical. ∎

## 6. Testing Strategy

### Compilation Test

Verify that all 4 language grammars compile under both feature configurations:

```sh
# Serial (default)
cargo test --workspace

# Parallel
cargo test --workspace --features ascent-parallel
```

### Semantic Equivalence Test

For each grammar, run the same set of inputs under both serial and parallel modes and assert identical outputs:

1. Parse a set of representative inputs.
2. Run `exec add` (fixpoint evaluation) under `ascent!`.
3. Run `exec add` under `ascent_par!`.
4. Assert that all output relations contain identical tuples.

### Regression

The F1 fix (eqrel clone-dereference) must not introduce regressions in serial mode. The `.clone()` on `&T` (serial) is a standard `Clone::clone` call that returns `T` — semantically identical to the original direct binding.

### Performance Benchmark

Compare `exec add` latency for the Rholang grammar (66 rules, 6 categories) under both modes:

```sh
# Serial baseline
cargo bench --bench bench_languages -- "rhocalc/exec_add"

# Parallel
cargo bench --bench bench_languages --features ascent-parallel -- "rhocalc/exec_add"
```

Expected: 2-4x speedup on machines with 4+ cores, depending on the number of independent strata and the size of the delta relations.

## 7. References

- Ceri, S., Gottlob, G. & Tanca, L. (1989). What you always wanted to know about Datalog (and never dared to ask). *IEEE TKDE*, 1(1):146-166.
- Bancilhon, F. & Ramakrishnan, R. (1986). An amateur's introduction to recursive query processing strategies. *SIGMOD Record*, 15(2):16-52.
- Ascent crate documentation: Semi-naive evaluation and `ascent_par!` parallel iteration.
- Rayon crate documentation: Data parallelism via work stealing.
