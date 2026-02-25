# Module 6: Procedural Macros - The Code Generator

**Goal**: Understand how `language!` transforms a definition into Rust code.

The `macros/` crate is the heart of MeTTaIL. It's a Rust **procedural macro** - a program that runs at compile time, receives your `language!` definition as input, and produces thousands of lines of Rust code as output.

---

## 6.1 Procedural Macros 101

### What Is a Proc Macro?

A procedural macro is a Rust function with this signature:

```rust
#[proc_macro]
pub fn language(input: TokenStream) -> TokenStream { ... }
```

- **Input**: A `TokenStream` - the raw tokens between `language! { ... }`
- **Output**: A `TokenStream` - the generated Rust code that replaces the macro call
- **When it runs**: At compile time, before type checking

The key libraries:
- **`syn`** - Parses `TokenStream` into a structured AST
- **`quote`** - Generates `TokenStream` from Rust-like template syntax
- **`proc_macro_error`** - Provides good error messages on invalid input

### The Entry Point

**File**: `macros/src/lib.rs`

```rust
#[proc_macro]
#[proc_macro_error]
pub fn language(input: TokenStream) -> TokenStream {
    // 1. Parse the DSL input into a LanguageDef struct
    let language_def = parse_macro_input!(input as LanguageDef);

    // 2. Validate (check types exist, variables are bound, etc.)
    if let Err(e) = validate_language(&language_def) {
        abort!(e.span(), "{}", e.message());
    }

    // 3. Generate AST types, parser, Display, substitution
    let ast_code = generate_all(&language_def);

    // 4. Generate freshness functions (for Ascent rewrite clauses)
    let freshness_fns = generate_freshness_functions(&language_def);

    // 5. Generate Ascent Datalog source
    let ascent_output = generate_ascent_source(&language_def);

    // 6. Generate metadata (for REPL introspection)
    let metadata_code = generate_metadata(&language_def);

    // 7. Generate Language trait implementation
    let language_code = generate_language_impl(&language_def, ...);

    // 8. Combine everything
    let combined = quote! {
        #ast_code
        #freshness_fns
        #ascent_code
        #metadata_code
        #language_code
    };

    TokenStream::from(combined)
}
```

Six stages, producing six pieces of code that get concatenated together.

---

## 6.2 Stage 1: Parsing the DSL (`ast/`)

### `LanguageDef` - The Internal Representation

**File**: `macros/src/ast/language.rs`

The `parse_macro_input!(input as LanguageDef)` call uses `syn`'s parsing infrastructure to transform raw tokens into:

```rust
pub struct LanguageDef {
    pub name: Ident,                          // "Calculator", "RhoCalc"
    pub options: HashMap<String, AttributeValue>, // DSL options
    pub types: Vec<LangType>,                 // Type declarations
    pub terms: Vec<GrammarRule>,              // Term constructors
    pub equations: Vec<Equation>,             // Structural equations
    pub rewrites: Vec<RewriteRule>,           // Reduction rules
    pub logic: Option<LogicBlock>,            // Custom Datalog (logic { ... })
}
```

### Grammar Rules

**File**: `macros/src/ast/grammar.rs`

Each term declaration like `AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;` becomes a `GrammarRule`:

```rust
pub struct GrammarRule {
    pub label: Ident,              // "AddInt"
    pub params: Vec<TermParam>,    // [(a, Int), (b, Int)]
    pub items: Vec<GrammarItem>,   // [NonTerminal(a), Terminal("+"), NonTerminal(b)]
    pub category: Ident,           // "Int"
    pub native_eval: Option<...>,  // Some(a + b)
    pub eval_mode: Option<...>,    // Some(Fold)
    pub associativity: Option<...>, // None (left) or Some(Right)
}
```

### Pattern Expressions

**File**: `macros/src/ast/pattern.rs` (the largest file in the macro crate)

Equation and rewrite patterns like `(PPar {(PInput n ^x.p), (POutput n q), ...rest})` are parsed into a tree of `Expr` nodes. This handles:
- Constructor application: `(POutput n q)`
- Collection patterns: `{..., ...rest}`
- Binding patterns: `^x.p`
- Substitution patterns: `(subst ^x.p N)`
- Variable references: `N`, `P`
- Spread/rest patterns: `...rest`

---

## 6.3 Stage 2: Validation (`ast/validation/`)

Before generating code, the macro validates the definition:

- **`validator.rs`** - Orchestrates all checks
- **`typechecker.rs`** - Infers and verifies categories
- **`error.rs`** - Error types with source spans

Checks include:
- All referenced categories exist in `types {}`
- All constructor names in patterns exist in `terms {}`
- Variables in equations/rewrites are properly bound
- Field types match their usage
- Freshness conditions reference actual bound variables

Errors point to the exact span in your `language!` definition, e.g.:
```
error: Unknown category 'Process' in term declaration
  --> languages/src/rhocalc.rs:25:5
```

---

## 6.4 Stage 3: Code Generation (`gen/`)

**File**: `macros/src/gen/mod.rs`

The `generate_all()` function orchestrates multiple generators:

```rust
pub fn generate_all(language: &LanguageDef) -> TokenStream {
    let ast_enums = generate_ast_enums(language);          // types/
    let flatten_helpers = generate_flatten_helpers(language); // term_ops/
    let normalize_impl = generate_normalize_functions(language); // term_ops/
    let subst_impl = generate_substitution(language);       // term_ops/
    let env_types = generate_environments(language);        // runtime/
    let env_subst_impl = generate_env_substitution(language); // runtime/
    let display_impl = generate_display(language);          // syntax/
    let generation_impl = generate_term_generation(language); // term_gen/
    let random_gen_impl = generate_random_generation(language); // term_gen/
    let eval_impl = generate_eval_method(language);         // native/
    let is_ground_impl = generate_is_ground_methods(language); // term_ops/
    let var_inference_impl = generate_var_category_inference(language); // syntax/
    let parser_code = generate_prattail_parser(language);   // syntax/parser/

    quote! { #ast_enums #flatten_helpers ... #parser_code }
}
```

### `gen/types/` - AST Enum Generation

Produces the Rust enum for each language type. For `Proc` in RhoCalc, this generates:

```rust
#[derive(Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd, BoundTerm)]
pub enum Proc {
    PZero,
    PDrop(Box<Name>),
    PPar(HashBag<Proc>),
    POutput(Box<Name>, Box<Proc>),
    PInputs(Vec<Name>, Scope<Vec<Binder<String>>, Proc>),
    NQuote(Box<Proc>),  // cross-category cast
    PNew(Scope<Vec<Binder<String>>, Proc>),
    Err,
    CastInt(Box<Int>),
    // ... native ops, lambda/apply variants, var variant
    PVar(OrdVar),
    LamProc(Scope<Binder<String>, Proc>),
    ApplyProc(Box<Proc>, Box<Proc>),
}
```

Note the `#[derive(BoundTerm)]` - this is from moniker and auto-generates the variable traversal code.

### `gen/syntax/` - Parser and Display

- **`display.rs`** - Generates `impl Display for Proc { fn fmt(...) { match self { ... } } }`
- **`parser/prattail_bridge.rs`** - Converts `LanguageDef` to `prattail::LanguageSpec` and calls the PraTTaIL parser generator
- **`var_inference.rs`** - Generates variable type inference from parse context

### `gen/term_ops/` - Term Operations

- **`subst.rs`** - Capture-avoiding substitution for each category pair
- **`normalize.rs`** - Beta-reduction of lambda applications, collection flattening
- **`ground.rs`** - `is_ground()` check (no free variables)

### `gen/runtime/` - Language Trait Implementation

- **`language.rs`** - Generates `impl Language for FooLanguage { ... }` tying everything together
- **`metadata.rs`** - Generates metadata structs for REPL introspection
- **`environment.rs`** - Generates environment types and operations

---

## 6.5 Stage 4: Ascent Generation (`logic/`)

**File**: `macros/src/logic/mod.rs`

Generates the Ascent Datalog program. This is covered in detail in Module 8, but the structure is:

```rust
pub fn generate_ascent_source(language: &LanguageDef) -> AscentSourceOutput {
    let relations = generate_relations(language);        // relations.rs
    let category_rules = generate_category_rules(language);  // categories.rs
    let equation_rules = generate_equation_rules(language);  // equations.rs
    let rewrite_rules = generate_rewrite_rules(language);    // rewrites/
    let custom_logic = language.logic.content;            // user's logic { ... } block

    quote! {
        #relations
        #category_rules
        #equation_rules
        #rewrite_rules
        #custom_logic
    }
}
```

---

## 6.6 Inspecting Generated Code

### Looking at Generated Files

The Ascent Datalog code is written to files in `languages/src/generated/`:

```
languages/src/generated/
  rhocalc-datalog.rs      (~80KB)
  calculator-datalog.rs   (~110KB)
  ambient-datalog.rs      (~25KB)
  lambda-datalog.rs       (~5KB)
```

These are Rust source files with the raw Ascent rules. Open one to see what the macro produces.

### Using `cargo expand`

If you install `cargo-expand`, you can see *all* generated code (not just the Datalog files):

```bash
cargo install cargo-expand
cargo expand -p mettail-languages > expanded.rs
```

Warning: this produces a *very* large file (hundreds of thousands of lines).

### Adding Debug Output

You can add `eprintln!` or `println!` in the macro code to see what's happening at compile time:

```rust
// In macros/src/lib.rs:
eprintln!("Generating language: {}", language_def.name);
eprintln!("  Types: {:?}", language_def.types.len());
eprintln!("  Terms: {:?}", language_def.terms.len());
```

These print during `cargo build`, not at runtime.

---

## 6.7 The Module Map

```
macros/src/
├── lib.rs              # Entry point: language! macro
├── ast/                # Parse the DSL into structured types
│   ├── language.rs     # LanguageDef (top-level struct)
│   ├── grammar.rs      # GrammarRule, TermParam, GrammarItem
│   ├── pattern.rs      # Expr (pattern language for equations/rewrites)
│   ├── types.rs        # TypeExpr, EvalMode, etc.
│   ├── validation/     # Semantic validation
│   │   ├── validator.rs
│   │   ├── typechecker.rs
│   │   └── error.rs
│   └── tests.rs        # Compile tests
├── gen/                # Generate Rust code from AST
│   ├── mod.rs          # generate_all() orchestration
│   ├── types/          # Enum generation
│   ├── syntax/         # Parser + Display
│   │   ├── parser/     # PraTTaIL bridge
│   │   ├── display.rs
│   │   └── var_inference.rs
│   ├── term_ops/       # Substitution, normalization
│   ├── native/         # Native eval support
│   ├── runtime/        # Language trait, metadata, environment
│   ├── term_gen/       # Test utilities
│   └── blockly/        # Visual block generation
└── logic/              # Ascent Datalog generation
    ├── mod.rs          # Main orchestration
    ├── relations.rs    # Relation declarations
    ├── categories.rs   # Term exploration rules
    ├── equations.rs    # Equality axioms
    ├── rewrites/       # Rewrite rule generation
    ├── congruence/     # Congruence closure
    ├── rules.rs        # Helper functions
    ├── helpers.rs      # AST helpers
    ├── common.rs       # Shared utilities
    └── writer.rs       # File output
```

---

## Exercises

### Exercise 1: Trace the Entry Point

Read `macros/src/lib.rs`. List the six stages of code generation and what each produces.

### Exercise 2: Read `LanguageDef`

Open `macros/src/ast/language.rs`. What fields does `LanguageDef` have? For each field, identify where it comes from in a `language!` definition.

### Exercise 3: Explore Generated Code

Open `languages/src/generated/calculator-datalog.rs`. Find:
1. The relation declarations
2. A deconstruction rule (extracting subterms)
3. A native eval rule
4. A congruence rule

Try to match each back to the Calculator's `language!` definition.

### Exercise 4: The Quote Trick

The `quote!` macro in the code generator is itself a macro that generates code. Find an example of `quote!` in `macros/src/gen/` and trace what Rust code it produces.

---

## Checkpoint

Before moving on, make sure you can:

1. **Explain** what a procedural macro does (input tokens → output tokens)
2. **Name** the six stages of code generation in `macros/src/lib.rs`
3. **Describe** what `LanguageDef` contains and how it maps to `language!` syntax
4. **Find** generated code in `languages/src/generated/`
5. **Navigate** the `macros/src/` directory structure

---

**Next**: [Module 7: The PraTTaIL Parser Generator](07-prattail-parser.md) - How syntax declarations become parsers
