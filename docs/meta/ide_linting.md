# Dealing with Rust-Analyzer Linting Errors

## Expected Errors You Can Ignore

### In Theory Files (`theories/src/*.rs`)

**Warnings you'll see:**
```
- non_local_definitions warning (from derive macro)
- failed to resolve: unresolved import
- type annotations needed
- no method named `iter` found
```

**Why:** The `theory!` macro generates complex code that rust-analyzer doesn't fully expand during IDE analysis.

**Resolution:** These files compile correctly. The errors are IDE-only.

### In Example Files (`examples/*.rs`)

**Errors you'll see:**
```
- method `to_rel_index_write` exists for unit type `()`
- no method named `len` found for unit type `()`
- comparison errors
```

**Why:** The `ascent_run!` macro expands at compile time. Rust-analyzer sees `()` instead of the expanded types.

**Resolution:** The examples compile and run correctly. The errors are IDE-only.

## Verification

To verify everything works despite IDE errors:

```bash
# Build everything
cargo build --workspace

# Run examples
cargo run --example rholang_demo
cargo run --example ambient_demo

# Run REPL
cargo run --bin mettail
```

If these commands succeed, your code is correct!

## Suppressing Warnings in VS Code/Cursor

Create `.vscode/settings.json`:

```json
{
  "rust-analyzer.diagnostics.disabled": [
    "non-local-definitions"
  ],
  "rust-analyzer.diagnostics.warningsAsInfo": [
    "unresolved-import",
    "unresolved-macro-call"
  ]
}
```

Or suppress per-file by adding at the top of theory files:

```rust
#![allow(non_local_definitions)]
```

## Why This Happens

### Proc-Macro Expansion Limitations

Rust-analyzer has limited support for:
1. Complex proc-macros like `theory!`
2. Macro-generated macro calls (e.g., `lalrpop_mod!` inside `theory!`)
3. Multi-stage expansion (Ascent's `ascent_run!` → `include_source!`)

### This is Normal

Many Rust projects with heavy macro use have these IDE warnings:
- `serde` with custom derives
- `diesel` with query macros
- `rocket` with route macros

The code compiles correctly; IDE analysis is just incomplete.

## Quick Test

To verify your setup is working:

```bash
cd /Users/cbwells/Documents/GitHub/mettail-rust
cargo build --workspace && cargo run --example rholang_demo
```

If this succeeds, ignore the IDE errors! ✅

## Alternative: Disable Specific Checks

In each theory file, add at the top:

```rust
// Suppress IDE warnings from macro expansion
#![allow(non_local_definitions)]
#![allow(unused_imports)]
```

But this isn't necessary - the warnings don't affect compilation.

