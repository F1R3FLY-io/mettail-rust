# Proposal: Decouple the `rholang` interpreter from the parser (feature-gate the compiler)

**Status:** DRAFT for the f1r3node-rust maintainer to review/apply. Authored from the
MeTTaIL (M-RHO) integration side. **Not yet applied** — `rholang` is f1r3node-rust's
crate and is mid-migration; this is a coordination artifact, not a change MeTTaIL makes.

## Goal

Let *interpreter-only* consumers depend on `rholang` **without compiling
`rholang_parser`**. MeTTaIL's bridge crates need only the Rho machine (the reducer,
RSpace, matcher, cost accounting); they build `rhoapi::Par` AST directly and never
parse Rholang text. Today they transitively compile `rholang_parser` purely because
`rholang` is a monolithic crate. This is doubly undesirable because **MeTTaIL's own
parser is intended to replace the rholang-rs parser** — pulling the old parser into
the toolchain is backwards.

Concrete near-term payoff: MeTTaIL drops the transitive parser dependency **and** the
temporary `[patch]` that currently pins `rholang_parser` to the
`rholang-rs-cost-accounting-transpiler` worktree (added only to keep `rholang`'s
in-flight cost-accounting code compiling — see [`Cargo.toml`](../../../../Cargo.toml)).

## Findings (verified against `f1r3node-rust/rholang/src/rust/interpreter`)

| Observation | Evidence |
|---|---|
| `rholang_parser` is used **only** under `interpreter/compiler/**` | 415 `rholang_parser` references, all under `interpreter/compiler/` (parser, normalizer, cost_accounting) |
| `compiler` is a clean sibling `pub mod` | `interpreter/mod.rs`: `pub mod compiler;` is a peer of `reduce`, `rho_runtime`, `matcher`, `accounting`, `substitute`, `dispatch`, `storage` |
| The execution core is parser-free at the module level | `reduce.rs`, `rho_runtime.rs`, `matcher/`, `accounting/`, `external_services.rs` contain **no** `use …compiler` |
| Cross-references **into** `compiler::` from outside it are only three sites | `interpreter.rs` (`use compiler::Compiler`, the from-source `evaluate`), `pretty_printer.rs` (`compiler::normalize…`), `test_utils/*` (test helpers) |
| The runtime can init **without** the compiler | `create_rho_runtime(init_registry: bool)`: with `init_registry: false` no registry bootstrap runs ("for some test cases you don't need the registry") |
| MeTTaIL's bridge is a pure inject-`Par` consumer | `mettail-rho-runtime/src/run.rs`: "MeTTaIL only emits the `Par` program and reads the resting data"; it uses `create_rho_runtime` + reduce/inject, never `evaluate(source)` |

What the bridge actually imports from `rholang` (all interpreter, no compiler):

```
mettail-rho-runtime → rholang::rust::interpreter::{
    rho_runtime::{create_rho_runtime, RhoRuntime},
    matcher::r#match::Matcher, external_services::ExternalServices,
    accounting::costs::Cost }
mettail-rho-adapter → rholang::rust::interpreter::accounting::{
    delta_sigma::{DemandEntry, SigKey}, resource_logic::{GsltPresentation, OslfResourceLogic}, Sig }
```

## Proposed change (in `f1r3node-rust/rholang`)

### 1. Make the parser optional + add a `compiler` feature

```toml
# rholang/Cargo.toml
[dependencies]
rholang-parser = { git = "…rholang-rs", rev = "c163755", optional = true }

[features]
default = ["compiler"]          # backward-compatible: existing consumers unchanged
compiler = ["dep:rholang-parser"]
# interpreter-only consumers select `default-features = false`
```

### 2. Gate the compiler submodule

```rust
// rholang/src/rust/interpreter/mod.rs
#[cfg(feature = "compiler")]
pub mod compiler;
```

### 3. Gate the three leak points (keep the inject-`Par`/reduce path always available)

```rust
// interpreter.rs — the from-source entry only
#[cfg(feature = "compiler")]
use crate::rust::interpreter::compiler::Compiler;
// … #[cfg(feature = "compiler")] on the evaluate(source) methods;
//    leave inject(Par) / reduce / create_rho_runtime ungated.

// pretty_printer.rs — gate the normalize-based paths (or the whole module if it is
// only used for source round-tripping / debugging).
#[cfg(feature = "compiler")]
use crate::rust::interpreter::compiler::normalize::{normalize_ann_proc, ProcVisitOutputs};

// test_utils/{par_builder_util,utils}.rs — gate behind `compiler` (they call Compiler).
#[cfg(feature = "compiler")]
```

`rho_runtime.rs`: keep `create_rho_runtime`, `inject`, `reduce` ungated; gate only the
`evaluate(source)` method (line ~114) behind `compiler`. `bootstrap_registry` is already
behind the `init_registry` flag — verify it constructs the registry `Par` without the
parser (see open items).

### 4. MeTTaIL side (after the above lands)

```toml
# mettail-rho-runtime/Cargo.toml, mettail-rho-adapter/Cargo.toml
rholang = { workspace = true, default-features = false }   # interpreter only → no rholang_parser
```

Then MeTTaIL's root-`Cargo.toml` `[patch."…rholang-rs"]` is **deleted** — the parser is
no longer in MeTTaIL's dependency graph at all, so the version skew that motivated it
cannot recur.

## Open items the implementer verifies

1. **Registry bootstrap source.** Does `registry::registry_bootstrap::ast` build the
   registry `Par` from a pre-normalized AST, or does it invoke the compiler? If the
   latter, either gate `bootstrap_registry` behind `compiler` (interpreter-only
   consumers call `create_rho_runtime(init_registry = false)`) or pre-bake the registry
   `Par` so it needs no parser.
2. **`pretty_printer` for interpreter-only consumers.** If anything in the parser-free
   execution path needs pretty-printing, confirm it does not route through
   `compiler::normalize`; otherwise provide a parser-free printer or gate the callers.
3. **System processes.** Confirm `system_processes` / `rho_type` construct their `Par`
   directly (no parser); the grep shows no `rholang_parser` there, so this is expected
   to be clean.

## Why this is safe + backward-compatible

`default = ["compiler"]` means every current consumer of `rholang` is unaffected (the
compiler stays on by default). Only consumers that *opt out*
(`default-features = false`) drop the parser — and they are exactly the inject-`Par`
consumers that never used it. The change is additive (a feature boundary), not a
refactor of execution logic.

## Relationship to the parser-replacement roadmap

This decoupling is the prerequisite that lets MeTTaIL's WPDA/prattail parser become the
sole Rholang front-end: once interpreter-only consumers no longer pull `rholang_parser`,
MeTTaIL→`rhoapi::Par`→Rho-machine is a parser-free pipeline on the MeTTaIL side, and the
eventual replacement of the rholang-rs parser is a change isolated to the (now
feature-gated, default-on) `compiler` module rather than the whole `rholang` crate.
