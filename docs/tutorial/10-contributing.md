# Module 10: Contributing - Your First Change

**Goal**: Make a real contribution to MeTTaIL.

---

## 10.1 Development Workflow

### Build and Test

```bash
# Build (dev profile, Cranelift backend - fast compile, slower runtime)
cargo build

# Run all tests
cargo test

# Run tests for a specific crate
cargo test -p mettail-languages
cargo test -p prattail
cargo test -p mettail-runtime

# Run a specific test by name
cargo test -p mettail-languages comm

# Run the REPL
cargo run -- rhocalc

# Run benchmarks (release profile, LLVM backend)
cargo bench -p mettail-languages

# Generate docs
cargo doc --open
```

### Git Workflow

```bash
git checkout -b feature/my-change
# make changes
cargo test
git add -A
git commit -m "description of change"
git push -u origin feature/my-change
# open PR on GitHub
```

### Compile Times

MeTTaIL's proc macros generate a lot of code. First builds are slow (~2-5 minutes). Subsequent builds are faster because Cargo only recompiles changed crates.

If you change `macros/`, everything downstream recompiles. If you only change `repl/`, just the binary recompiles.

The Cranelift backend (dev profile) saves significant compilation time compared to LLVM.

---

## 10.2 Common Pitfalls

### Forgetting `clear_var_cache()`

When writing tests, always call `mettail_runtime::clear_var_cache()` before parsing a new independent term. Without this, variables from previous tests leak through and cause subtle equality bugs.

```rust
#[test]
fn my_test() {
    mettail_runtime::clear_var_cache();  // Always first!
    let term = Proc::parse("@(0)?x.{*(x)}").unwrap();
    // ...
}
```

### Nightly-Only Features

The project requires Rust nightly. If you get errors about `codegen-backend`, make sure `rustup` installed the nightly toolchain with the cranelift component. Running any cargo command in the project directory should auto-install via `rust-toolchain.toml`.

### Linker Errors

If you get linker errors on macOS, make sure `lld` is installed and in your PATH:
```bash
brew install llvm
export PATH="/opt/homebrew/opt/llvm/bin:$PATH"  # Apple Silicon
```

If you can't install `lld`, you can comment out the linker lines in `.cargo/config.toml`.

### Large Generated Files

Files in `languages/src/generated/` are auto-generated and can be 80-110KB. Don't edit them manually - they're overwritten on every build. Changes go in the `macros/` crate.

### Macro Debugging

To debug the proc macro:
1. Add `eprintln!` in `macros/src/` (prints during compilation)
2. Check `languages/src/generated/*.rs` for the Ascent output
3. Use `cargo expand -p mettail-languages` to see all generated code (very large output)

---

## 10.3 Project Structure for Contributors

```
Where to make changes:

Adding a new language      → languages/src/my_lang.rs + repl/src/registry.rs
Adding a REPL command      → repl/src/repl.rs
Adding a REPL example      → repl/src/examples/
Fixing parser generation   → prattail/src/
Fixing macro codegen       → macros/src/gen/
Fixing Datalog generation  → macros/src/logic/
Fixing runtime types       → runtime/src/
Adding tests               → languages/tests/
Adding benchmarks          → languages/benches/
Updating docs              → docs/
```

---

## 10.4 Suggested First Contributions

Ordered from easiest to hardest:

### Easy: Add a Calculator Operator

Add `Abs`, `Min`, `Max`, or `Gcd` to the Calculator language.

1. Open `languages/src/calculator.rs`
2. Add the term declaration:
   ```rust
   Abs . a:Int |- "abs" "(" a ")" : Int ![a.abs()] step;
   ```
3. Add a congruence rule:
   ```rust
   AbsCong . | S ~> T |- (Abs S) ~> (Abs T);
   ```
4. Test: `cargo test -p mettail-languages`
5. Try in REPL: `exec abs(-5)`

### Easy: Add a REPL Example

Add a new combinator to `repl/src/examples/rhocalc.rs`. Ideas:
- A "tee" that duplicates a message to two channels
- A "counter" that sends incrementing numbers

### Easy: Add a Test Case

Look at `languages/tests/rhocalc_tests.rs` and find an untested scenario. Write a test using the existing helpers (`assert_reduces_to`, `assert_no_rewrites`, etc.).

### Medium: Define a New Simple Language

Create a new language definition. Ideas:
- **Boolean algebra**: Just `Bool` type with `And`, `Or`, `Not`, `Implies` and De Morgan's laws as equations
- **Simple lambda calculus**: `Expr` type with `Var`, `Lam`, `App` and beta-reduction
- **Arithmetic with Let**: `Expr` type with `Let x = e1 in e2` binding

Steps:
1. Create `languages/src/my_lang.rs` with `language! { ... }`
2. Add `pub mod my_lang;` to `languages/src/lib.rs`
3. Register in `repl/src/registry.rs`
4. Add tests in `languages/tests/`

### Medium: Improve the REPL

- Add a `count` command (show term/rewrite/normal-form counts)
- Add a `history` command (show all visited terms)
- Improve error messages for common mistakes
- Add tab completion for commands

### Hard: Work on Logic Generation

The `macros/src/logic/` module has TODOs:
- Conjunction of premises in rewrite rules
- Equation congruence for terms with collections and bindings
- Generic common relations (path, normal_form, etc.)

### Hard: Build a Rholang Subset

Define a larger language that includes more Rholang features:
- Pattern matching in receives
- Persistent sends (`n!!(q)`)
- Conditional processes

---

## 10.5 Current TODO List

From `docs/to_do.md`:

```
- Update main docs (architecture/main_goals are 2 months old)
- Complete logic generation (conjunction of premises, eq congruence for collections/bindings)
- Fix bugs (REPL display types of free/bound vars)
- Improve term generation (guide by redex formation)
- Improve REPL (make any result the new current_term, display auto-generated logic)
- Build more languages (Rholang, MeTTaIL, Rust)
- Code improvement (split up ast_code, phase out BNF, replace "category" with "lang_type")
- Performance (optimize Datalog rules, laziness, ascent_par!)
- RSpace integration
- Language composition
- Language translation
```

---

## 10.6 Reading the Code: Tips

### Start from the Outside In

1. Read `repl/src/main.rs` (tiny - just creates REPL and runs it)
2. Read `repl/src/repl.rs` (command dispatch - see how commands work)
3. Read `languages/src/calculator.rs` (simplest language definition)
4. Read `runtime/src/language.rs` (the `Language` trait that ties everything together)
5. Then go deeper as needed into `macros/`, `prattail/`, etc.

### Use the REPL as a Learning Tool

The REPL is the best way to understand what a language definition produces:

```
lang calculator
types          -- see all types
exec 2 + 3     -- see parsing + evaluation
rewrites       -- see rewrite graph
relations      -- see custom Datalog relations
typeof 2 + x   -- see type inference
```

### Grep for Patterns

When you want to understand how something works:

```bash
# Find where a concept is implemented
rg "fn run_ascent" --type rust
rg "HashBag" --type rust -l
rg "COMM\|Comm" --type rust

# Find test examples
rg "assert_reduces_to" --type rust

# Find all language definitions
rg "language!" --type rust -l
```

### Read Tests First

Tests are often the best documentation. They show:
- What inputs are valid
- What outputs are expected
- Edge cases and known behaviors

Start with `languages/tests/rhocalc_tests.rs` - it's well-organized by feature area.

---

## 10.7 Architecture Decisions to Know About

### Why Datalog Instead of Direct Interpretation?

Datalog (via Ascent) gives you:
- **Exhaustive exploration** - finds ALL reachable terms, not just one execution path
- **Efficient joins** - shared variables in patterns are handled by indexed joins
- **Equation support** - equivalence classes come from `eqrel` for free
- **Custom queries** - users can write arbitrary Datalog queries over the rewrite graph

Trade-off: Ascent computes eagerly (all terms, all rewrites). For large term spaces, this can be slow. The roadmap includes lazy evaluation and parallel execution (`ascent_par!`).

### Why Moniker Instead of De Bruijn Indices?

Moniker provides:
- **Alpha-equivalence** checking (structurally correct)
- **Capture-avoiding substitution** (correct by construction)
- **Derive macros** for traversal (less boilerplate)

De Bruijn indices would be faster but much harder to get right, especially with the multi-binder patterns MeTTaIL supports.

### Why Cranelift for Dev Builds?

The Cranelift codegen backend compiles Rust code ~2.7x faster than LLVM, at the cost of ~2.7x slower runtime. Since proc macros generate enormous amounts of code, the compilation speedup matters a lot during development.

---

## Exercises

### Exercise 1: Build and Test

```bash
cargo test
```

Do all tests pass? If not, investigate why.

### Exercise 2: Make a Change

Pick one of the "Easy" tasks from section 10.4 and implement it. Create a branch, make the change, run tests, and commit.

### Exercise 3: Explore the TODO List

Read `docs/to_do.md` and pick one item that interests you. Open the relevant source files and understand the current state. What would need to change? Write a brief plan (even if you don't implement it).

### Exercise 4: Review an Existing Test

Open `languages/tests/rhocalc_tests.rs`. Pick a test module (e.g., `comm`, `native_ops`). For each test:
1. What does it test?
2. What input does it use?
3. What output does it expect?
4. Can you think of a case that isn't tested?

---

## You've Completed the Tutorial!

If you've worked through all 10 modules, you now understand:

1. **Rust fundamentals** needed for this codebase (Module 1)
2. **The big picture** - what MeTTaIL does and why (Module 2)
3. **Runtime types** - `Language`, `Term`, `HashBag`, `Scope` (Module 3)
4. **Simple language definitions** - the Calculator (Module 4)
5. **Complex language definitions** - RhoCalc with binding (Module 5)
6. **Code generation** - how the `language!` macro works (Module 6)
7. **Parser generation** - PraTTaIL (Module 7)
8. **Datalog rewriting** - Ascent engine (Module 8)
9. **The REPL** - interactive exploration (Module 9)
10. **Contributing** - making changes (Module 10)

The best way to deepen your understanding is to **start contributing**. Pick a task, dive in, and ask questions when you get stuck. Welcome to MeTTaIL!
