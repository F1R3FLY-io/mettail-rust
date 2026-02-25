# Module 1: Rust Foundations

**Goal**: Get comfortable enough with Rust to read and modify MeTTaIL code.

This module won't teach you all of Rust - it focuses specifically on the Rust features that appear most frequently in this codebase. If you've never written Rust at all, spend a day or two with [The Rust Book](https://doc.rust-lang.org/book/) chapters 1-10 first. Then come back here.

---

## 1.1 Setting Up: Toolchain and Build

### Installing Rust

If you don't have Rust yet:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

MeTTaIL uses the **nightly** toolchain (for the Cranelift codegen backend). You don't have to install it manually - the project's `rust-toolchain.toml` tells `rustup` to handle it automatically:

```toml
# rust-toolchain.toml
[toolchain]
channel = "nightly"
components = ["rustc-codegen-cranelift-preview"]
```

When you run any `cargo` command in this project, `rustup` will:
1. Download the nightly compiler if needed
2. Install the Cranelift codegen component
3. Use them for all builds

### Building and Running

```bash
cd mettail-rust

# Build everything (first build takes a while - downloading deps + compiling)
cargo build

# Run the REPL
cargo run

# Run all tests
cargo test

# Run tests for a specific crate
cargo test -p mettail-languages
```

### Why Nightly?

Rust has three release channels: **stable**, **beta**, and **nightly**. Most Rust projects use stable. MeTTaIL uses nightly because:

- **Cranelift backend**: Dev builds use the Cranelift code generator instead of LLVM. Cranelift compiles Rust code much faster (at the cost of slower runtime). This matters because MeTTaIL's procedural macros generate a *lot* of code.
- Release/bench builds still use LLVM for maximum runtime performance.

You can see this in `Cargo.toml`:

```toml
[profile.dev]
codegen-backend = "cranelift"  # Fast compile, slower runtime

[profile.release]
codegen-backend = "llvm"       # Full LLVM optimization
```

### Linker Setup (macOS)

The project also uses a fast linker. On macOS, you need `lld`:

```bash
brew install llvm
# Then ensure llvm/bin is in your PATH:
# Apple Silicon: export PATH="/opt/homebrew/opt/llvm/bin:$PATH"
# Intel Mac:     export PATH="/usr/local/opt/llvm/bin:$PATH"
```

If you skip this, builds will still work but linking will be slower.

### Workspace Structure

MeTTaIL is a **Cargo workspace** - multiple crates in one repository. Open `Cargo.toml` at the root:

```toml
[workspace]
members = ["macros", "runtime", "languages", "repl", "prattail", "ascent_syntax_export", "query"]
```

Each member is its own crate with its own `Cargo.toml`. They can depend on each other:

```
macros/       - The language! proc macro (the heart of the project)
runtime/      - Shared traits and types (Language, Term, HashBag, etc.)
languages/    - Language definitions that use the macro (RhoCalc, Calculator, etc.)
repl/         - The interactive REPL binary
prattail/     - Custom parser generator
query/        - Datalog-style query executor
ascent_syntax_export/ - Vendored Ascent parser for code generation
```

**Exercise**: Run `cargo run` and try these REPL commands:
```
lang rhocalc
exec {}
exec { @(0)!({}) | @(0)?x.{*(x)} }
```

---

## 1.2 Ownership, Borrowing, and Lifetimes

This is the core Rust concept. If you're new to Rust, this is where you'll spend the most time.

### The Short Version

In Rust, every value has exactly one **owner**. When the owner goes out of scope, the value is dropped (freed). You can:

- **Move** ownership: `let b = a;` (now `a` is invalid)
- **Borrow** immutably: `let r = &a;` (read-only reference, `a` still valid)
- **Borrow** mutably: `let r = &mut a;` (read-write reference, exclusive access)

### Where You'll See This in MeTTaIL

**`Box<dyn Term>`** - The most common pattern. A `Box` is a heap-allocated value with a single owner. `dyn Term` means "any type that implements the `Term` trait." This is how MeTTaIL handles terms generically:

```rust
// runtime/src/language.rs
pub trait Language: Send + Sync {
    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String>;
    //                                          ^^^^^^^^^^^^^^
    //                  Owned, heap-allocated, dynamically-dispatched term
}
```

**`&self` and `&dyn Term`** - Borrowed references. Most methods take `&self` (immutable borrow of the struct) or `&dyn Term` (borrowed reference to a trait object):

```rust
fn run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String>;
//            ^^^^^        ^^^^^^^^^
//       borrow self    borrow the term (don't take ownership)
```

**`.clone()`** - When you need a copy. Since Rust enforces single ownership, you'll see `.clone()` when code needs its own copy:

```rust
let new_term = term.clone_box();  // Clone a trait object into a new Box
let name = name.clone();          // Clone a String
```

### What to Remember

- If the compiler says "value moved here", you're trying to use something after giving it away. Add `.clone()` where needed.
- If it says "cannot borrow as mutable", you have a shared reference (`&`) where you need an exclusive one (`&mut`).
- `Box<dyn Trait>` = owned trait object on the heap. This is the main way MeTTaIL handles polymorphism at runtime.

---

## 1.3 Enums and Pattern Matching

Enums and `match` are the backbone of MeTTaIL. Every language's AST is represented as enums, and every operation on terms uses pattern matching.

### Rust Enums (Unlike C/Java Enums)

Rust enums can carry data:

```rust
// This is what the language! macro generates for RhoCalc (simplified):
enum Proc {
    PZero,                           // No data (the null process)
    PDrop(Box<Name>),                // Carries a Name
    PPar(HashBag<Proc>),             // Carries a multiset of Procs
    POutput(Box<Name>, Box<Proc>),   // Carries a Name and a Proc
    PNew(Scope<Binder<String>, Proc>), // Carries a binding scope
    CastInt(Box<Int>),               // Carries a native integer
    // ...
}
```

Each variant can hold different types and amounts of data. This is how MeTTaIL represents every term in a language.

### Pattern Matching with `match`

```rust
match term {
    Proc::PZero => println!("The null process"),
    Proc::PDrop(name) => println!("Dereference: *{}", name),
    Proc::PPar(bag) => println!("Parallel: {} processes", bag.len()),
    Proc::POutput(name, body) => println!("Send on {}", name),
    _ => println!("Something else"),  // catch-all
}
```

The compiler forces you to handle *all* variants (or use `_` as a catch-all). This is a major safety feature - when you add a new variant, the compiler tells you every place that needs updating.

### `if let` for Single-Variant Checks

When you only care about one variant:

```rust
if let Proc::PPar(bag) = term {
    // bag is available here
    for (elem, count) in bag.iter() {
        // process each element
    }
}
```

This pattern appears constantly in the generated Datalog code:

```rust
// Generated Ascent rule:
proc(field) <-- proc(t), if let Proc::PDrop(field) = t;
```

### Nested Pattern Matching

You can destructure deeply:

```rust
match term {
    Proc::POutput(name, body) => {
        if let Name::NQuote(inner_proc) = name.as_ref() {
            // inner_proc is the process inside the quote
        }
    }
    _ => {}
}
```

### Where Pattern Matching Appears in MeTTaIL

1. **Generated AST code** - Every `Display`, substitution, and normalization method matches on all variants
2. **Rewrite rules** - The Ascent Datalog engine uses `if let` to match term patterns
3. **Native evaluation** - The `![...]` blocks in language definitions use `match` on operands
4. **REPL commands** - The command dispatcher matches on user input

---

## 1.4 Traits and Trait Objects

Traits are Rust's version of interfaces. MeTTaIL uses them to abstract over different languages.

### Defining a Trait

```rust
// runtime/src/language.rs (simplified)
pub trait Term: fmt::Display + fmt::Debug + Send + Sync {
    fn clone_box(&self) -> Box<dyn Term>;
    fn term_id(&self) -> u64;
    fn term_eq(&self, other: &dyn Term) -> bool;
    fn as_any(&self) -> &dyn Any;
}
```

This says: "Any type that implements `Term` must provide these four methods, and must also implement `Display`, `Debug`, `Send`, and `Sync`."

### Implementing a Trait

The `language!` macro generates trait implementations for each language's types. Conceptually:

```rust
impl Term for Proc {
    fn clone_box(&self) -> Box<dyn Term> {
        Box::new(self.clone())
    }
    fn term_id(&self) -> u64 {
        // hash-based ID
    }
    // ...
}
```

### Trait Objects (`dyn Trait`)

When the REPL doesn't know *which* language is loaded at compile time, it uses trait objects:

```rust
// repl/src/state.rs
struct ReplState {
    current_term: Option<Box<dyn Term>>,   // Could be Proc, Name, Int...
    // ...
}
```

`Box<dyn Term>` means "a heap-allocated value of some type that implements `Term`." The compiler doesn't know the concrete type - method calls go through a virtual dispatch table (like C++ virtual methods).

### The `Language` Trait

The most important trait in the project:

```rust
pub trait Language: Send + Sync {
    fn name(&self) -> &'static str;
    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String>;
    fn run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String>;
    fn create_env(&self) -> Box<dyn Any + Send + Sync>;
    // ... 15+ more methods
}
```

Each language (RhoCalc, Calculator, etc.) implements this trait. The REPL stores a `Box<dyn Language>` and calls methods on it without knowing which concrete language it is.

### `Any` for Downcasting

Sometimes you need to go from a trait object back to a concrete type. The `as_any()` method enables this:

```rust
fn as_any(&self) -> &dyn Any;

// Usage:
if let Some(proc) = term.as_any().downcast_ref::<Proc>() {
    // Now we have a concrete Proc
}
```

---

## 1.5 Error Handling: Result and `?`

MeTTaIL uses two error handling patterns:

### `Result<T, E>`

```rust
fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
    //                                 ^^^^^^^^^^^^^^^^^^^^^^^^^^
    //                           Ok(term) on success, Err(message) on failure
}
```

### The `?` Operator

The `?` operator propagates errors up the call stack:

```rust
fn load_language(&mut self, name: &str) -> Result<()> {
    let language = self.registry.get(name)?;  // Returns early if Err
    self.state.set_language(language)?;         // Returns early if Err
    Ok(())                                      // Everything succeeded
}
```

Without `?`, you'd need explicit `match`:

```rust
let language = match self.registry.get(name) {
    Ok(lang) => lang,
    Err(e) => return Err(e),
};
```

### `anyhow`

The REPL uses the `anyhow` crate for flexible error handling:

```rust
use anyhow::Result;  // Result<T> is shorthand for Result<T, anyhow::Error>

fn run(&mut self) -> Result<()> {
    // anyhow::Error can hold any error type
}
```

---

## 1.6 Common Collections and Iterators

### `HashMap<K, V>`

Used extensively for:
- Variable caches (`HashMap<String, FreeVar<String>>`)
- Environment bindings
- Relation data in `AscentResults`

```rust
use std::collections::HashMap;

let mut map = HashMap::new();
map.insert("x", 42);

if let Some(value) = map.get("x") {
    println!("x = {}", value);
}
```

### `Vec<T>`

The most common collection. Used for:
- Lists of terms, rewrites, equivalence classes
- Generated code stores everything in `Vec`

### Iterators and Closures

Rust's iterator API is used heavily:

```rust
// From rhocalc_tests.rs:
fn normal_form_displays(results: &AscentResults) -> Vec<String> {
    results.normal_forms()
        .iter()                              // iterate over normal forms
        .map(|nf| nf.display.clone())       // transform each to its display string
        .collect()                           // collect into a Vec
}
```

Common iterator methods you'll see:
- `.iter()` - iterate by reference
- `.map(|x| ...)` - transform each element
- `.filter(|x| ...)` - keep elements matching a predicate
- `.collect()` - gather into a collection
- `.any(|x| ...)` - check if any element matches
- `.find(|x| ...)` - find the first matching element
- `.flat_map(|x| ...)` - map and flatten nested iterators

---

## 1.7 Derive Macros

You'll see `#[derive(...)]` on almost every type:

```rust
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HashBag<T: Clone + Hash + Eq> {
    counts: HashMap<T, usize>,
    total_count: usize,
}
```

What each derive does:
- **`Clone`** - Enables `.clone()` (deep copy)
- **`Debug`** - Enables `{:?}` formatting (for debugging)
- **`PartialEq`/`Eq`** - Enables `==` comparison
- **`Hash`** - Enables use as HashMap key / in HashSet
- **`Ord`/`PartialOrd`** - Enables `<`, `>`, sorting

MeTTaIL needs all of these because terms must be:
- Cloneable (for substitution, creating new terms)
- Comparable (for Datalog relations, equivalence checking)
- Hashable (for HashBag, Ascent's internal hash tables)

---

## 1.8 Procedural Macros (Preview)

This is an advanced topic covered fully in Module 6, but here's the concept:

A **procedural macro** is a Rust function that receives code as input and produces code as output. It runs at compile time. MeTTaIL's `language!` macro is a procedural macro:

```rust
// You write this:
language! {
    name: Calculator,
    types { ![i32] as Int },
    terms { AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold; },
    // ...
}

// The macro generates thousands of lines of Rust code:
// - enum Int { NumLit(i32), IVar(OrdVar), AddInt(Box<Int>, Box<Int>), ... }
// - impl Display for Int { ... }
// - impl Int { pub fn parse(input: &str) -> Result<Int, String> { ... } }
// - impl Language for CalculatorLanguage { ... }
// - ascent! { struct CalculatorAscent; ... (Datalog rules) }
// - ... etc
```

The `macros/` crate is where this transformation happens. The generated code ends up in `languages/src/generated/`.

---

## Checkpoint

Before moving on, make sure you can:

1. **Build and run** the project: `cargo run` launches the REPL
2. **Read enum definitions** and understand which variant carries which data
3. **Read `match` expressions** and understand which branch handles which case
4. **Read trait definitions** and understand the interface contract
5. **Read `Box<dyn Trait>`** and understand it's a heap-allocated trait object
6. **Read `Result<T, E>` and `?`** and understand error propagation
7. **Read iterator chains** like `.iter().map(...).filter(...).collect()`

You don't need to be an expert at writing any of this yet - the goal is to be able to *read* the codebase. Writing comes with practice.

---

**Next**: [Module 2: The Big Picture](02-big-picture.md) - Understanding what MeTTaIL does and why
