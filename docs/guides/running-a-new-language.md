# Running Programs on a New Language

This guide walks you from a modular `.rho` language specification to actually running programs — either interactively in the REPL or programmatically from Rust.

It applies to languages authored with the **MeTTaIL Unified Specification (MUS)** pipeline on the `modules` branch. For background on how modules compose, see [module-system-diagrams.md](../design/exploring/module-system-diagrams.md).

---

## Who this guide is for

| Role | Goal |
|------|------|
| **Language author** | Turn `.rho` specs into a compiled language (parser + rewrite engine) |
| **End user** | Parse terms, evaluate or rewrite them, explore in the REPL or embed in Rust |

Both roles converge on the same runtime: generated `language!` code produces a `{Name}Language` type that implements `mettail_runtime::Language`.

---

## Overview

```text
.rho specs  →  mettail-spec  →  language! Rust  →  cargo build  →  parse / rewrite / REPL
```

The modular path does **not** replace the runtime stack. It changes **how** the parser and rewrite rules are authored — layered `.rho` files instead of a single hand-written macro block.

---

## Part 1 — Make the language runnable (author)

### Step 1: Finish the `.rho` module graph

Your language needs an **entry file** that exports a shipped language binding:

```rholang
export language MyLang = SomeExtender(...)
```

**Reference example:** `languages/specs/mycalc/`

| File | Role |
|------|------|
| `numbers.rho` | Base extender (`FloatBase`) |
| `complex.rho` | Extension extender (`Complex(Base)`) |
| `app.rho` | Entry file: `export language MyCalc = M.Complex(N.FloatBase())` |

Validate the spec before building:

```bash
cargo run -p mettail-spec -- compile path/to/app.rho --language MyLang
```

This prints an NTIR summary (language name, types, terms, content hash). Fix assembly or import errors here first.

**Optional — inspect projected Rust on stdout:**

```bash
cargo run -p mettail-spec -- project path/to/app.rho --language MyLang
```

---

### Step 2: Project to Rust

**Option A — CLI (manual):**

```bash
cargo run -p mettail-spec -- project path/to/app.rho --language MyLang --out mylang_lang.rs
```

**Option B — `build.rs` (recommended for workspace languages):**

Follow the MyCalc pattern in `languages/build.rs`:

```rust
mettail_spec::project_rust_file(
    manifest_dir.join("specs/mylang/app.rho"),
    Some("MyLang"),
    out_dir.join("mylang_lang.rs"),
)?;
```

Add `cargo:rerun-if-changed=…` for each `.rho` file so Cargo rebuilds when specs change.

---

### Step 3: Wire into the `languages` crate

Create a thin wrapper module (see `languages/src/mycalc.rs`):

```rust
//! MyLang generated from `.rho` specs (see `specs/mylang/` and `build.rs`).

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

include!(concat!(env!("OUT_DIR"), "/mylang_lang.rs"));
```

Register the module in `languages/src/lib.rs`:

```rust
pub mod mylang;
```

The projected file contains `language! { name: MyLang, … }`. The macro generates:

- AST types and parser (PraTTaIL)
- Ascent rewrite engine
- **`MyLangLanguage`** implementing `mettail_runtime::Language`

---

### Step 4: Build

```bash
cargo build -p mettail-languages
```

Or build the full workspace:

```bash
cargo build
```

If projection or macro expansion fails, fix the `.rho` spec or projected output and rebuild.

---

### Step 5: Register in the REPL (manual today)

Built-in languages are registered in `repl/src/registry.rs`. Currently registered: RhoCalc, Calculator, Lambda, Ambient.

**MyCalc and other `.rho`-authored languages are not registered automatically.** To use the REPL interactively, add:

```rust
use mettail_languages::mylang::MyLangLanguage;

registry.register(Box::new(MyLangLanguage));
```

in `build_registry()`.

Until this step is done, use the Rust API or tests (Part 2, Option 2).

---

### Step 6: Smoke-test

Minimum integration test (pattern from `languages/tests/mycalc_rho.rs`):

```rust
use mettail_languages::mylang::MyLangLanguage;
use mettail_runtime::Language;

#[test]
fn mylang_compiles_and_exposes_metadata() {
    let lang = MyLangLanguage;
    assert_eq!(lang.name(), "MyLang");
    assert!(!lang.metadata().types().is_empty());
}
```

Run:

```bash
cargo test -p mettail-languages mylang
```

For parity against a monolithic golden spec, see `mettail-spec/tests/parity_test.rs`.

---

## Part 2 — Run programs (end user)

Once the language is built (and optionally REPL-registered), use one of the paths below.

### Option 1 — REPL (best for exploration)

For languages already in the registry (RhoCalc, Calculator, Lambda, Ambient):

```bash
cargo run -- rhocalc          # start with RhoCalc loaded
# or
cargo run                     # then: lang rhocalc
```

**Typical session:**

```text
mettail> lang rhocalc
Loading language: rhocalc
rhocalc> exec 3 + 5
rhocalc> step new x in { x!(0) }
rhocalc> apply 0
rhocalc> x = 42
rhocalc> env
rhocalc> help
```

**Useful commands:**

| Command | Purpose |
|---------|---------|
| `languages` | List registered languages |
| `lang <name>` | Load a language |
| `exec <term>` | Direct evaluation → result |
| `step <term>` | Step-by-step; then `apply <N>` |
| `normal-forms` | Show normal forms of current term |
| `rewrites` | List rewrites from current term |
| `<name> = <term>` | Bind a name in the environment |
| `load-env <file>` | Load bindings from a file |
| `example <name>` | Run a registered example |
| `help` | Full command list |

For a **new** language after Step 5 above:

```bash
cargo run -- mylang
# or: lang mylang
```

See also [repl.md](./repl.md) for the full REPL reference.

---

### Option 2 — Rust program or test (best for automation)

Pattern from `languages/tests/calculator.rs`:

```rust
use mettail_languages::mylang::MyLangLanguage;
use mettail_runtime::Language;

fn run_program(input: &str) -> Result<(), String> {
    mettail_runtime::clear_var_cache();
    let lang = MyLangLanguage;

    // Parse source text in your language
    let term = lang.parse_term(input)?;

    // Run the rewrite engine
    let results = lang.run_ascent(term.as_ref())?;

    // Inspect normal forms
    for nf in results.normal_forms() {
        println!("{}", nf.display);
    }

    Ok(())
}
```

If your language implements native evaluation (like Calculator), the REPL's `exec` command uses `try_direct_eval`; you can call that from Rust as well.

Run tests:

```bash
cargo test -p mettail-languages
```

---

### Option 3 — Example files (REPL batch mode)

Existing languages ship example programs under `repl/src/examples/` (e.g. `rhocalc.txt`, `calculator` examples).

In the REPL:

```text
list-examples
example rhocalc-patterns
```

For a new language, add examples under `repl/src/examples/` and register them in `repl/src/examples/mod.rs`. This is extra wiring — not generated automatically from `.rho` yet.

---

## End-to-end checklist

```text
□ Write .rho modules → export language L in entry file
□ cargo run -p mettail-spec -- compile … --language L   (validate NTIR)
□ build.rs projects → language! Rust in OUT_DIR
□ languages/src/<lang>.rs includes projected output
□ pub mod <lang> in languages/src/lib.rs
□ cargo build -p mettail-languages
□ Register <Lang>Language in repl/src/registry.rs     (for REPL)
□ cargo test -p mettail-languages                     (smoke / parity)
□ Run:
    REPL:  cargo run -- <lang>  →  exec <term>
    Rust:  parse_term → run_ascent
```

---

## Worked example: MyCalc

MyCalc is the reference modular language on this branch.

**Specs:** `languages/specs/mycalc/{numbers,complex,app}.rho`  
**Wrapper:** `languages/src/mycalc.rs`  
**Build hook:** `languages/build.rs` → `OUT_DIR/mycalc_lang.rs`

After `cargo build`:

```rust
use mettail_languages::mycalc::MyCalcLanguage;
use mettail_runtime::Language;

let lang = MyCalcLanguage;
let term = lang.parse_term("...");  // syntax from your terms { ... } blocks
let results = lang.run_ascent(term.as_ref().unwrap()).unwrap();
```

MyCalc's current spec defines `Float`, `Cmplx`, `CmplxInj`, and `CmplxAdd`. Add literals and rewrites in the `.rho` chain before `exec`-style evaluation produces meaningful numeric results.

---

## What is not wired yet

| Feature | Status on `modules` branch |
|---------|----------------------------|
| `export space s: MyLang` | Declared in `.rho`; no runtime channel/process runner yet |
| Auto REPL registration from `.rho` | Manual `registry.register(...)` required |
| Standalone binary per language | Embed via `languages` crate + REPL or your own binary |
| Rholang process code in modules | Island parsing exists (Phase 3); full process execution on spaces is future work |

**Bottom line:** "Run my program" today means **parse a term in your language's syntax and drive the rewrite/eval engine** — not yet "deploy a Rholang process on a typed space."

---

## Related documents

| Document | Focus |
|----------|-------|
| [module-system-diagrams.md](../design/exploring/module-system-diagrams.md) | Architecture diagrams and pipeline phases |
| [module-system-design-v1.md](../design/exploring/module-system-design-v1.md) | MUS design, NTIR, islands |
| [modules-in-languages-design.md](../design/exploring/modules-in-languages-design.md) | GSLT alignment, phasing |
| [repl.md](./repl.md) | REPL command reference |
| [macros.md](./macros.md) | `language!` macro and codegen |
| `languages/specs/mycalc/` | Reference `.rho` module graph |
