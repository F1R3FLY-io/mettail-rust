# Migrating from LALRPOP to PraTTaIL

> **Migration complete.** LALRPOP was fully removed in Phase 3. PraTTaIL is now the
> sole parser backend. This document is kept for historical reference.

**Step-by-step guide for migrating MeTTaIL's parser pipeline from LALRPOP-generated
LR(1) parsers to PraTTaIL-generated Pratt + RD parsers.**

---

## Overview

MeTTaIL's original parsing pipeline generates `.lalrpop` grammar files from
`language!` macro definitions, then compiles them with the LALRPOP compiler into
Rust LR(1) parsers. PraTTaIL replaces this entire pipeline with a single Rust
library that generates parser code directly from the `LanguageSpec`, eliminating
the `.lalrpop` intermediate step and all 4 categories of LALRPOP workarounds.

```
BEFORE (LALRPOP pipeline):

  language! { ... }
       |
       v
  macros/gen/syntax/parser/lalrpop.rs    (generates .lalrpop files)
       |
       v
  languages/src/generated/*.lalrpop      (intermediate grammar files)
       |
       v
  LALRPOP compiler (build.rs)            (generates Rust LR(1) parsers)
       |
       v
  ~20,000 lines of generated parser code


AFTER (PraTTaIL pipeline):

  language! { ... }
       |
       v
  macros/gen/syntax/parser/ -> PraTTaIL  (direct code generation)
       |
       v
  ~1,500-2,000 lines of generated parser code
```

---

## Feature Comparison

| Feature | LALRPOP | PraTTaIL |
|---|---|---|
| **Parser type** | LR(1) / LALR(1) | Pratt + Recursive Descent |
| **Generated code size** | ~20,000 lines | ~1,500-2,000 lines |
| **Build dependency** | `lalrpop` crate (build-dep) + `lalrpop-util` (runtime) | None (proc-macro2 + quote only) |
| **Intermediate files** | `.lalrpop` files in `src/generated/` | None |
| **Build step** | `build.rs` compiles `.lalrpop` | Direct proc-macro expansion |
| **Multi-type variables** | Requires type prefixes (`bool:x`) | Requires type prefixes (same) |
| **Operator precedence** | Tiered productions (3 levels per category) | Binding power pairs (unlimited levels) |
| **Cross-category rules** | Atom-tier placement with manual wiring | FIRST set dispatch with automatic backtracking |
| **Lambda parsing** | Primary-category-only with type inference | Primary-category-only with type inference (same) |
| **Keyword handling** | `match {}` blocks | DFA priority system |
| **Lexer** | LALRPOP built-in regex lexer | Automata-optimized (NFA->DFA->minimize) |
| **Error messages** | LALRPOP default | Custom with position information |
| **Unary minus** | Disabled (shift-reduce conflict) | Can be supported (prefix handler) |
| **Parse complexity** | O(n) | O(n) |

---

## What Does NOT Change

### The `language!` Macro Syntax

The `language!` macro syntax remains **completely unchanged**. All existing language
definitions continue to work as-is:

```rust
// This file does NOT change
language! {
    name: Calculator,
    types {
        ![i32] as Int
        ![bool] as Bool
    },
    terms {
        Add . a:Int, b:Int |- a "+" b : Int ![a + b] step;
        Eq . a:Int, b:Int |- a "==" b : Bool ![a == b] step;
        // ...
    },
    equations { },
    rewrites { },
}
```

### The AST Types

The generated AST enums (`Int`, `Bool`, `Proc`, `Name`, etc.) have the same
structure, same variants, and same types. Code that pattern-matches on AST nodes
does not need to change.

### The `parse()` Entry Point

The `Cat::parse(input)` method signature is identical:

```rust
// Same API before and after migration
let result = Int::parse("3 + 4")?;
let result = Proc::parse("{}")?;
```

### The REPL User Experience

The REPL commands, variable binding, and evaluation all remain the same. The
`pre_substitute_env` workaround for non-primary variables is still needed (it
addresses a fundamental multi-type variable ambiguity, not a LALRPOP limitation).

---

## Step-by-Step Migration

### Step 1: Update the Macro Crate

The `mettail-macros` crate currently generates `.lalrpop` grammar files via
`macros/src/gen/syntax/parser/lalrpop.rs`. Replace this code path with a call
to PraTTaIL's `generate_parser()`.

**File:** `macros/src/gen/syntax/parser/mod.rs`

Before:
```rust
mod lalrpop;
mod writer;
pub use lalrpop::*;
pub use writer::*;
```

After:
```rust
mod prattail_bridge;   // New module that calls mettail_prattail::generate_parser()
mod writer;            // May still be needed for non-parser generation
pub use prattail_bridge::*;
pub use writer::*;
```

**New file:** `macros/src/gen/syntax/parser/prattail_bridge.rs`

```rust
use mettail_prattail::{generate_parser, LanguageSpec, CategorySpec, RuleSpec, ...};

/// Convert the macro's internal LanguageDef AST to PraTTaIL's LanguageSpec.
pub fn generate_parser_code(language: &LanguageDef) -> proc_macro2::TokenStream {
    let spec = convert_to_language_spec(language);
    generate_parser(&spec)
}

fn convert_to_language_spec(lang: &LanguageDef) -> LanguageSpec {
    LanguageSpec {
        name: lang.name.to_string(),
        types: lang.types.iter().enumerate().map(|(i, t)| CategorySpec {
            name: t.name.to_string(),
            native_type: t.native_type_name(),
            is_primary: i == 0,
        }).collect(),
        rules: /* ... map grammar rules to RuleSpec ... */,
    }
}
```

### Step 2: Add PraTTaIL as a Dependency

**File:** `macros/Cargo.toml`

```toml
[dependencies]
mettail-prattail = { path = "../prattail" }
# ... keep proc-macro2, quote, syn ...
```

### Step 3: Remove LALRPOP Build Step

**File:** `languages/build.rs`

Before:
```rust
fn main() {
    lalrpop::Configuration::new()
        .set_in_dir("src/generated")
        .process()
        .unwrap();
}
```

After:
```rust
fn main() {
    // PraTTaIL generates parser code at macro expansion time.
    // No build step needed.

    // Keep any non-parser build steps (e.g., lang-gen for Datalog).
}
```

### Step 4: Remove LALRPOP Dependencies

**File:** `languages/Cargo.toml`

Remove:
```toml
# Remove these:
# lalrpop-util = { workspace = true, features = ["lexer"] }

# [build-dependencies]
# lalrpop = { workspace = true }
```

**File:** `Cargo.toml` (workspace root)

Remove from `[workspace.dependencies]`:
```toml
# Remove these if no longer used anywhere:
# lalrpop = "0.20"
# lalrpop-util = "0.20"
```

### Step 5: Remove Generated LALRPOP Files

The `.lalrpop` files in `languages/src/generated/` are no longer needed:

```
languages/src/generated/rhocalc.lalrpop      <- remove
languages/src/generated/calculator.lalrpop   <- remove
languages/src/generated/lambda.lalrpop       <- remove
languages/src/generated/ambient.lalrpop      <- remove
```

Keep the non-LALRPOP generated files (Datalog, expanded Rust, etc.) if they are
still used.

### Step 6: Update Language Source Files

The `.rs` files under `languages/src/` (e.g., `rhocalc.rs`, `calculator.rs`) should
**not need changes** -- the `language!` macro interface is unchanged.

However, verify that any imports of LALRPOP-generated modules are removed:

Before:
```rust
// In languages/src/lib.rs (if it existed)
lalrpop_mod!(pub rhocalc, "/generated/rhocalc.rs");
```

After:
```rust
// No LALRPOP module imports needed -- parser is generated inline by the macro
```

### Step 7: Update the REPL

**File:** `repl/src/repl.rs`

The REPL's `pre_substitute_env` function remains unchanged -- it addresses a
fundamental multi-type ambiguity that affects both LALRPOP and PraTTaIL.

Remove any LALRPOP-specific error handling:

Before:
```rust
use lalrpop_util::ParseError;
match result {
    Err(ParseError::UnrecognizedToken { .. }) => { ... }
}
```

After:
```rust
// PraTTaIL returns plain String errors
match result {
    Err(msg) => println!("Parse error: {}", msg),
}
```

**File:** `repl/Cargo.toml`

Remove LALRPOP dependencies if present:
```toml
# Remove:
# lalrpop-util = { workspace = true }
```

### Step 8: Verify

Run the test suite:

```bash
# Unit tests for PraTTaIL itself
cargo test -p mettail-prattail

# Integration tests for languages
cargo test -p mettail-languages

# Full workspace
cargo test --workspace

# REPL smoke test
echo "exec 3 + 4" | cargo run -- --language calculator
```

### Step 9: Compare Generated Code Size

To verify the migration achieved the expected code reduction:

```bash
# Before: check size of LALRPOP-generated parsers
wc -l languages/src/generated/*.lalrpop

# After: inspect PraTTaIL output (expand macros)
cargo expand -p mettail-languages 2>/dev/null | wc -l
```

Expected: ~10-14x reduction in generated parser code.

---

## Eliminated LALRPOP Workarounds

After migration, the following workarounds documented in
`docs/design/made/lalrpop-parser-limitations.md` are no longer needed:

### 1. Tiered Productions (Cat / CatInfix / CatAtom)

LALRPOP required splitting each category into three non-terminals to handle
operator precedence without `%left`/`%right` declarations.

**PraTTaIL**: Binding power pairs handle unlimited precedence levels natively in
the Pratt loop. No tiered productions needed.

### 2. `match {}` Keyword Blocks

LALRPOP required explicit `match {}` blocks to give keyword tokens (like `"bool"`,
`"error"`, `"true"`) priority over the identifier regex.

**PraTTaIL**: The DFA assigns `priority()` values to token kinds. Keywords
(priority 10) automatically beat identifiers (priority 1) through the maximal
munch + priority resolution in `resolve_accept()`.

### 3. Cross-Category Infix Guards

LALRPOP required careful detection of cross-category infix rules to prevent them
from being placed in the wrong tier (e.g., `Int "==" Int : Bool` must not go in
`BoolInfix`).

**PraTTaIL**: Cross-category rules are classified separately and handled by the
dispatch module with FIRST set analysis. The Pratt loop only contains same-category
infix operators.

### 4. Var+Terminal Top-Level Partitioning

LALRPOP required special placement of rules starting with `Var Terminal ...` at
the top level to avoid shift-reduce conflicts with bare variable rules.

**PraTTaIL**: The prefix handler's match statement naturally gives precedence to
specific terminal tokens over the variable fallback. No special partitioning
needed.

---

## Potential Differences

### Error Messages

LALRPOP's error messages reference token positions in terms of the regex lexer.
PraTTaIL's error messages reference byte positions in the input. The error format
changes from LALRPOP's `ParseError` enum to plain `String` messages.

### Maximal Munch Edge Cases

LALRPOP's regex-based lexer and PraTTaIL's DFA-based lexer may differ in edge
cases with overlapping token patterns. For example, if `"="` and `"=="` are both
terminals, LALRPOP uses regex priority rules while PraTTaIL uses DFA maximal munch.
Both produce the same result for standard grammars, but unusual patterns should be
tested.

### Unary Minus

With LALRPOP, unary minus was disabled due to shift-reduce conflicts with binary
minus. PraTTaIL can support unary minus as a prefix handler in `parse_<Cat>_prefix`,
since the prefix/infix distinction is natural in Pratt parsing. This can be enabled
as a post-migration improvement.

---

## Rollback Plan

If issues arise during migration, the rollback is straightforward:

1. Restore `lalrpop.rs` as the active parser generator in `macros/src/gen/syntax/parser/mod.rs`
2. Restore LALRPOP dependencies in Cargo.toml files
3. Restore `languages/build.rs` LALRPOP compilation step
4. Restore `.lalrpop` files (they should still be in git history)

The `language!` macro definitions themselves need no changes in either direction.
