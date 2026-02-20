# Compilation Performance Optimization

## Executive Summary

MeTTaIL's dev build time was reduced from **8m 49s to ~55s** (9.5x faster), and test
builds from **~22 minutes to ~1m 44s** (~13x faster). The root cause was a
monomorphization explosion in Ascent Datalog code generation: 13 independent
`ascent_run!` macro invocations across 4 languages produced 4.6 million lines of LLVM
IR and 92,991 monomorphized function copies. The primary fix consolidated these into 4
named `ascent!` structs (one per language), reducing monomorphizations by 69%.
Secondary build tooling optimizations (Cranelift codegen backend, mold linker, reduced
debug info) contribute an additional ~5s savings.

| Metric | Before | After | Speedup |
|--------|--------|-------|---------|
| Clean `cargo build` | 8m 49s | ~55s | 9.5x |
| `cargo test --workspace` (clean) | ~22 min | ~1m 44s | ~13x |

All 315 tests pass (16 ignored) after the changes.

---

## Root Cause Analysis

### Profiling Methodology

Three profiling tools were used to diagnose the bottleneck:

1. **`-Z self-profile`**: Rust compiler self-profiling, analyzed with the `summarize`
   tool. Produces per-phase timing data (typeck, codegen, linking, etc.).
   ```bash
   RUSTFLAGS="-Z self-profile" cargo build
   # Produces .mm_profdata files per crate in the target directory
   summarize summarize <profdata_file>
   ```

2. **`cargo-llvm-lines`**: Counts LLVM IR lines and monomorphized function copies per
   generic instantiation.
   ```bash
   cargo llvm-lines -p mettail-languages
   ```

3. **Ascent source inspection**: Examining the generated Datalog code to count
   `ascent_run!` invocations per language.

### Primary Root Cause: Ascent Macro Monomorphization Explosion

The `mettail-languages` crate was the compilation bottleneck, with `typeck` consuming
**504.93 seconds (77.7% of total compilation time)**. The cause: each syntactic
category in each language invoked `ascent_run!` independently, creating an anonymous
struct that was fully monomorphized in isolation.

#### `ascent_run!` Invocations Per Language

| Language | Categories | `ascent_run!` Invocations | Ascent Source Lines |
|----------|-----------|--------------------------|---------------------|
| Calculator | Int, Float, Bool, Str | 4 | 1,884 |
| RhoCalc | Proc, Name, Int, Float, Bool, Str | 6 | 1,687 |
| Ambient | Proc, Name | 2 | 449 |
| Lambda | Term | 1 | 112 |
| **Total** | | **13** | **4,132** |

Each invocation created an independent anonymous Ascent struct. The compiler
monomorphized each struct and all its generic dependencies (iterators, hash tables,
vectors) separately, even though many shared the same concrete types.

#### LLVM IR Output

`cargo-llvm-lines` for `mettail-languages` showed:

- **Total: 4,605,902 lines of LLVM IR, 92,991 monomorphized function copies**

Top contributors by LLVM IR lines:

| Function | Lines | % | Copies |
|----------|-------|---|--------|
| `rhocalc::run_ascent_typed::{{closure}}` | 345,373 | 7.5% | 1,754 |
| `core::slice::iter::Iter::fold` | 266,120 | 5.8% | 3,008 |
| `rhocalc::run_ascent_typed::{{closure}}^2` | 254,166 | 5.5% | 798 |
| `calculator::run_ascent_typed::{{closure}}` | 238,361 | 5.2% | 1,166 |
| `core::slice::iter::Iter::for_each` | 224,200 | 4.9% | 4,484 |
| `rhocalc::run_ascent_typed::{{closure}}^3` | 208,452 | 4.5% | 1,428 |
| `FlattenCompat::iter_fold` | 204,020 | 4.4% | 2,020 |
| `Iterator::fold` | 199,757 | 4.3% | 3,736 |
| `calculator::run_ascent_typed::{{closure}}^2` | 155,720 | 3.4% | 472 |
| `hashbrown::raw::RawIterRange::fold_impl` | 151,992 | 3.3% | 944 |

The top two language-specific entry points alone (`rhocalc` + `calculator` closures)
accounted for 583,734 lines (12.7%) of total LLVM IR.

### Secondary Root Cause: LLVM Code Generation

With 4.6M lines of IR to process, the LLVM backend consumed significant time:

| LLVM Phase | Self-Time |
|------------|-----------|
| `LLVM_module_codegen_emit_obj` | 43.20s |
| `LLVM_passes` | 13.53s |
| `LLVM_module_codegen` (scheduling) | 3.21s |
| `LLVM_module_optimize` | 1.56s |
| **Total LLVM Backend** | **~59s** |

### Tertiary Root Cause: Debug Info Generation

`compute_debuginfo_type_name` consumed 872ms processing 529,431 items. Full debug info
amplifies the LLVM codegen work.

### Complete Self-Profile Breakdown (`mettail-languages`)

| Phase | Self-Time | % of Total | Item Count |
|-------|-----------|------------|------------|
| `typeck` | 504.93s | 77.7% | 11,656 |
| `LLVM_module_codegen_emit_obj` | 43.20s | 6.7% | 180 |
| `region_scope_tree` | 24.50s | 3.8% | 11,656 |
| `codegen_module` | 13.96s | 2.1% | 180 |
| `LLVM_passes` | 13.53s | 2.1% | 1 |
| `mir_borrowck` | 9.95s | 1.5% | 1,550 |
| `expand_proc_macro` | 6.34s | 1.0% | 47 |
| All other phases | ~33s | 5.1% | -- |

Self-profile data sizes confirm `mettail-languages` as the bottleneck:

| Crate | Profile Data Size |
|-------|------------------|
| mettail-languages | 296 MB |
| mettail-macros | 34 MB |
| mettail-prattail | 24 MB |
| mettail-runtime | 12 MB |

---

## Optimizations Applied

### Optimization 1: `ascent_run!` to `ascent!` Named Struct (Major)

**Impact: 529s to 59s (89% reduction, 9.0x speedup)**

Each `ascent_run!` invocation was replaced with a single `ascent!` struct definition per
language. Instead of N independent anonymous structs (one per category), each language
now defines one named struct that contains all relations and rules.

| Language | Before (`ascent_run!`) | After (`ascent!`) | Reduction |
|----------|----------------------|-----------------|-----------|
| Calculator | 4 | 1 | 75% |
| RhoCalc | 6 | 1 | 83% |
| Ambient | 2 | 1 | 50% |
| Lambda | 1 | 1 | 0% |
| **Total** | **13** | **4** | **69%** |

**Semantics are preserved**: each `run_ascent()` call creates fresh state, inserts the
same initial facts, runs the same fixpoint computation, and reads the same results. The
only difference is that the struct type is named and shared across categories within a
language.

#### Implementation Details

**Files changed:**
- `macros/src/gen/runtime/language.rs` -- Replaced per-category `ascent_run!` blocks with
  a single `ascent! { struct AscentFoo; ... }` definition, plus `run_ascent_typed()`
  that instantiates, seeds, and runs the named struct.
- `macros/src/logic/mod.rs` -- Added `AscentSourceOutput.raw_content` field containing
  raw Ascent relations + rules (without the `ascent_source!` wrapper), suitable for
  direct inclusion in `ascent! { struct Foo; #raw_content }`.
- `macros/src/lib.rs` -- Passes `raw_content` through to `generate_language_impl()`.

#### Implementation Challenge: `include_source!` Failure

The initial approach tried to use `ascent!` with the existing `include_source!` callback
mechanism:
```rust
ascent! {
    struct AscentFoo;
    include_source!(my_source);
}
```

This **fails** inside proc-macro output because `include_source!` is itself a macro that
gets expanded during proc-macro execution, but the `ascent!` invocation in the output is
not expanded until the downstream crate compiles. The callback doesn't exist in the
downstream crate's scope.

**Solution**: Pass the raw Ascent content (relations + rules) directly as a
`TokenStream`, bypassing the callback mechanism entirely:
```rust
ascent! {
    struct AscentFoo;
    #raw_ascent_content  // TokenStream injected directly
}
```

### Optimization 2: Cranelift Codegen Backend (Minor)

**Impact: ~3s savings (59s to 56s)**

Replaces LLVM code generation with the Cranelift backend for dev builds. Before the
`ascent!` change, LLVM codegen consumed ~59s processing 4.6M IR lines -- a major cost.
After the `ascent!` change reduced IR volume dramatically, the LLVM savings from
Cranelift are proportionally much smaller (~3s).

Cranelift produces slightly less optimized machine code than LLVM, so debug binaries may
run marginally slower at runtime. This is an acceptable trade-off for dev iteration speed.

**Configuration**: Auto-installed via `rust-toolchain.toml`:
```toml
[toolchain]
channel = "nightly"
components = ["rustc-codegen-cranelift-preview"]
```

On first `cargo build`, rustup reads `rust-toolchain.toml` and automatically downloads
the nightly toolchain and the cranelift component. No manual steps required.

For release builds where runtime performance matters:
```bash
RUSTFLAGS="" cargo build --release
```

### Optimization 3: Mold Linker (Minor)

**Impact: ~2s savings on library builds; more significant for test/benchmark binaries**

Fast linkers reduce the time spent in the linking phase. For library-only builds, linking
is a small fraction of total time, so the savings are modest. For test builds that
produce multiple binary artifacts, the cumulative linking savings are more noticeable.

| Platform | Linker | Installation |
|----------|--------|-------------|
| Linux | [mold](https://github.com/rui314/mold) | `sudo pacman -S mold` / `sudo apt install mold` / `sudo dnf install mold` |
| macOS | [lld](https://lld.llvm.org/) via LLVM | `brew install llvm` + add to PATH |

**Configuration**: See `.cargo/config.toml` for per-platform target sections.

**Note**: There is no Cargo-native way to conditionally apply linker settings. If the
fast linker is not installed, the build will fail with a linker error. The documentation
in `.cargo/config.toml` explains how to comment out the linker lines to fall back to
the default linker.

### Optimization 4: Reduced Debug Info (Minor)

**Impact: Included in the ~5s combined tooling savings**

Setting `debug = "line-tables-only"` in `[profile.dev]` reduces the debug info generated
by the compiler. Full debug info (`debug = 2`, the default) produces type names, variable
locations, and other metadata that adds to codegen work. Line-tables-only provides enough
info for backtraces and basic debugging while reducing `compute_debuginfo_type_name` work
(872ms on 529K items in the original profile).

---

## Measured Results

### Per-Optimization Isolated Build Times

All measurements are clean `cargo build` (library + binary) on the same machine with the
`ascent!` change in place. CPU governor set to `performance`. No concurrent builds.

| Configuration | Codegen | Linker | Debug Info | Wall Time |
|---------------|---------|--------|------------|-----------|
| All optimizations | Cranelift | mold | line-tables-only | **54.56s** |
| Cranelift only | Cranelift | default (ld) | line-tables-only | 56.09s |
| Mold only | LLVM | mold | line-tables-only | 57.84s |
| Neither (debug tuning only) | LLVM | default (ld) | line-tables-only | 59.47s |
| **Original** (`ascent_run!` + LLVM) | LLVM | default (ld) | full | **529s** |

#### Analysis

- **`ascent!` change**: 529s to 59.47s = **469.5s saved (88.8%)**. This is the dominant
  optimization. It eliminated the monomorphization explosion that caused 77.7% of compile
  time.
- **Cranelift**: 59.47s to 56.09s = **3.4s saved (5.7%)**. Modest savings now that LLVM
  has much less IR to process.
- **Mold linker**: 59.47s to 57.84s = **1.6s saved (2.7%)**. Library linking is a small
  fraction of build time.
- **Combined tooling**: 59.47s to 54.56s = **4.9s saved (8.2%)**. The two tools are
  roughly additive.

### Test Build Results

| Metric | Before | After | Speedup |
|--------|--------|-------|---------|
| `cargo test --workspace` (clean) | ~22 min | ~1m 44s | ~13x |
| Tests passing | 229 | 315 | -- |
| Tests ignored | -- | 16 | -- |

---

## Developer Setup

### Prerequisites

1. **Nightly Rust toolchain with Cranelift** -- Automatically installed by
   `rust-toolchain.toml`. On first `cargo build`, rustup reads `rust-toolchain.toml` and
   downloads the nightly toolchain + cranelift component. No manual steps required.

2. **Fast linker** (optional but recommended):
   - **Linux**: Install mold
     ```bash
     # Arch Linux
     sudo pacman -S mold
     # Debian/Ubuntu
     sudo apt install mold
     # Fedora
     sudo dnf install mold
     ```
   - **macOS**: Install LLVM (provides lld)
     ```bash
     brew install llvm
     # Apple Silicon -- add to PATH:
     export PATH="/opt/homebrew/opt/llvm/bin:$PATH"
     # Intel Mac -- add to PATH:
     export PATH="/usr/local/opt/llvm/bin:$PATH"
     ```

### If Fast Linker Is Not Installed

If mold (Linux) or lld (macOS) is not installed, the build will fail with a linker error.
To fix this, comment out the `linker` and `link-arg` lines in `.cargo/config.toml` for
your platform:

```toml
[target.x86_64-unknown-linux-gnu]
# linker = "clang"
# rustflags = ["-C", "link-arg=-fuse-ld=mold", "-Zcodegen-backend=cranelift"]
rustflags = ["-Zcodegen-backend=cranelift"]
```

### Release Builds

For release builds where LLVM optimizations matter for runtime performance, override the
cranelift backend:

```bash
RUSTFLAGS="" cargo build --release
```

The `RUSTFLAGS` environment variable overrides `rustflags` in `.cargo/config.toml`.

### Troubleshooting

| Error | Cause | Fix |
|-------|-------|-----|
| `error: linker 'clang' not found` | clang not installed | Install clang (`sudo apt install clang`) |
| `cannot find -lmold` or mold linker error | mold not installed | Install mold or comment out linker lines |
| `error[E0463]: can't find crate for 'cranelift'` | cranelift component missing | Run `rustup component add rustc-codegen-cranelift-preview` |
| `No such file or directory` during codegen | Concurrent cargo builds sharing target dir | Kill stray `cargo`/`rustc` processes |

---

## Hardware

Benchmarks were run on:
- CPU: AMD Ryzen 9 9950X (16 cores / 32 threads, boosting to 5.7 GHz)
- RAM: 252 GB DDR5
- Storage: NVMe SSD
- OS: Arch Linux 6.18.9
- Governor: `performance` (fixed at max frequency)
