# Macros Crate Reorganization Plan

## Current Structure Analysis

### Module Overview

The `macros/` crate implements the `language!` procedural macro. The macro flow is:

```
language! { ... }
    ↓
syntax/      → Parse DSL into LanguageDef AST
    ↓
validation/  → Type check and validate
    ↓
codegen/     → Generate Rust code (AST types, operations, runtime)
datalog/     → Generate Ascent datalog rules
```

### Current Directory Layout

```
macros/src/
├── lib.rs                 # Entry point
├── syntax/                # DSL parsing (well-organized)
│   ├── language.rs        # LanguageDef, parsing
│   ├── grammar.rs         # GrammarRule, TermParam, SyntaxExpr
│   ├── types.rs           # TypeExpr, CollectionType
│   ├── term.rs            # Term expressions
│   └── pattern.rs         # Pattern matching
├── validation/            # Validation (well-organized)
│   ├── error.rs
│   ├── typechecker.rs
│   └── validator.rs
├── codegen/               # ← PROBLEMATIC
│   ├── mod.rs             # Helper functions
│   ├── ast_gen.rs         # 1474 lines, heterogeneous
│   ├── display.rs         # Display impl generation
│   ├── env.rs             # Environment types
│   ├── language.rs        # Language struct impl
│   ├── metadata.rs        # REPL metadata
│   ├── subst.rs           # 1638 lines, substitution
│   ├── parser/            # LALRPOP grammar gen (1802 lines)
│   │   ├── lalrpop.rs
│   │   └── writer.rs
│   ├── termgen/           # Term generation
│   │   ├── exhaustive.rs
│   │   └── random.rs
│   └── blockly/           # Visual blocks
│       ├── builder.rs
│       ├── colors.rs
│       └── writer.rs
├── datalog/               # Ascent generation (well-organized)
└── utils.rs               # Shared utilities
```

## Problems Identified

### 1. `codegen/ast_gen.rs` mixes unrelated concerns

At ~1474 lines, it handles:

| Function | Concern | Should Be |
|----------|---------|-----------|
| `generate_ast_enums()` | Core type definitions | `types/` |
| `generate_variant()` | Variant generation | `types/` |
| `generate_flatten_helpers()` | Collection normalization | `term_ops/` |
| `generate_normalize_functions()` | Deep normalization | `term_ops/` |
| `generate_eval_method()` | Native type evaluation | `native/` |
| `generate_var_category_inference()` | Parser lambda resolution | `syntax/` |

### 2. Parser and Display belong together

`codegen/parser/` and `codegen/display.rs` are inverse operations:
- Parser: text → AST
- Display: AST → text

Both are **syntax-layer** concerns, distinct from term operations.

### 3. Var inference supports parsing

`generate_var_category_inference()` produces `infer_var_category()` and `infer_var_type()` methods used by the parser to resolve which `Lam{Domain}` variant to construct. It belongs with syntax, not AST structure.

### 4. No clear module boundaries

The `codegen/` module mixes:
- Type definitions (AST enums)
- Syntax operations (parsing, display, var inference)
- Term operations (substitution, normalization)
- Native type handling (eval, literals)
- Runtime integration (Language trait, metadata)

---

## Proposed Reorganization

### Guiding Principles

| Category | Purpose | What it generates |
|----------|---------|-------------------|
| **Types** | Core AST structure | Rust enums, variants |
| **Syntax** | Text ↔ AST conversion | Parser, Display, inference helpers |
| **Term Ops** | Term manipulation | Substitution, normalization |
| **Native** | Native type support | Eval, literal handling (expandable) |
| **Runtime** | Language trait impl | Language struct, metadata |

### New Directory Structure

```
macros/src/
├── lib.rs                 # Entry point, orchestration
├── syntax/                # DSL parsing (UNCHANGED)
│   └── ...
├── validation/            # Validation (UNCHANGED)
│   └── ...
├── gen/                   # ALL code generation (RENAMED from codegen/)
│   ├── mod.rs             # Public API, shared helpers
│   │
│   ├── types/             # AST type generation
│   │   ├── mod.rs         # generate_ast() entrypoint
│   │   └── enums.rs       # Enum/variant generation
│   │
│   ├── syntax/            # Syntax-layer generation
│   │   ├── mod.rs
│   │   ├── parser/        # LALRPOP grammar
│   │   │   ├── mod.rs
│   │   │   ├── lalrpop.rs
│   │   │   └── writer.rs
│   │   ├── display.rs     # Display impls
│   │   └── var_inference.rs  # Lambda type inference (parsing support)
│   │
│   ├── term_ops/          # Term manipulation methods
│   │   ├── mod.rs
│   │   ├── subst.rs       # Capture-avoiding substitution
│   │   └── normalize.rs   # Flatten + normalize (merged)
│   │
│   ├── native/            # Native type support (expandable)
│   │   ├── mod.rs
│   │   └── eval.rs        # Native type eval()
│   │
│   ├── runtime/           # Runtime integration
│   │   ├── mod.rs
│   │   ├── language.rs    # Language struct, Term wrapper
│   │   └── metadata.rs    # REPL metadata
│   │
│   ├── termgen/           # Term generation
│   │   ├── mod.rs
│   │   ├── exhaustive.rs
│   │   └── random.rs
│   │
│   └── blockly/           # Visual blocks
│       ├── mod.rs
│       ├── builder.rs
│       ├── colors.rs
│       └── writer.rs
│
├── datalog/               # Ascent generation (UNCHANGED)
│   └── ...
└── utils.rs               # Shared utilities
```

### Module Responsibilities

#### `gen/types/` - AST Type Generation
Generates the core Rust enum types for a language.

- `enums.rs` - Enum definitions with all variants (Var, Literal, constructors, lambdas, etc.)

#### `gen/syntax/` - Parsing and Printing
Generates bidirectional text ↔ AST conversion and parsing support.

- `parser/lalrpop.rs` - LALRPOP grammar generation
- `parser/writer.rs` - File writing
- `display.rs` - `Display` trait implementations
- `var_inference.rs` - `infer_var_category()`, `infer_var_type()` for parser lambda resolution

#### `gen/term_ops/` - Term Manipulation
Generates methods for operating on terms.

- `subst.rs` - Capture-avoiding substitution (`substitute_*`, `subst`, etc.)
- `normalize.rs` - Collection canonicalization (flatten helpers + normalize method)

#### `gen/native/` - Native Type Support
Generates support for native Rust types mapped to language types. Designed for expansion.

- `eval.rs` - `.eval()` method for native type evaluation

#### `gen/runtime/` - Runtime Integration
Generates types implementing `mettail_runtime` traits.

- `language.rs` - `{Name}Language` struct, `{Name}Term` wrapper
- `metadata.rs` - `{Name}Metadata` for REPL introspection

#### `gen/termgen/` - Term Generation
Test/exploration utilities.

- `exhaustive.rs` - Enumerate all terms up to depth
- `random.rs` - Random term sampling

#### `gen/blockly/` - Visual Block Generation
Generates Blockly definitions for visual programming.

---

## Migration Steps

### Phase 1: Rename `codegen/` → `gen/`
Simple rename, update all imports in `lib.rs` and within `gen/`.

### Phase 2: Create `gen/types/`
1. Create `gen/types/` directory
2. Move enum generation from `ast_gen.rs` → `gen/types/enums.rs`
   - `generate_ast_enums()`
   - `generate_variant()`
   - `generate_variant_from_term_context()`
   - `generate_binder_variant()`
   - Helper functions for type conversion
3. Create `gen/types/mod.rs` with `generate_ast()` entrypoint

### Phase 3: Move syntax-related modules to `gen/syntax/`
1. Move `gen/parser/` → `gen/syntax/parser/`
2. Move `gen/display.rs` → `gen/syntax/display.rs`
3. Extract `generate_var_category_inference()` from `ast_gen.rs` → `gen/syntax/var_inference.rs`
4. Create `gen/syntax/mod.rs`

### Phase 4: Create `gen/term_ops/`
1. Move `gen/subst.rs` → `gen/term_ops/subst.rs`
2. Extract from `ast_gen.rs` → `gen/term_ops/normalize.rs`:
   - `generate_flatten_helpers()`
   - `generate_normalize_functions()`
3. Create `gen/term_ops/mod.rs`

### Phase 5: Create `gen/native/`
1. Create `gen/native/` directory
2. Extract `generate_eval_method()` from `ast_gen.rs` → `gen/native/eval.rs`
3. Create `gen/native/mod.rs`

### Phase 6: Create `gen/runtime/`
1. Move `gen/language.rs` → `gen/runtime/language.rs`
2. Move `gen/metadata.rs` → `gen/runtime/metadata.rs`
3. Move `gen/env.rs` → `gen/runtime/env.rs` (or `gen/term_ops/env.rs`?)
4. Create `gen/runtime/mod.rs`

### Phase 7: Update `gen/mod.rs` and `lib.rs`
Consolidate public API:

```rust
// gen/mod.rs
pub mod types;
pub mod syntax;
pub mod term_ops;
pub mod native;
pub mod runtime;
pub mod termgen;
pub mod blockly;

// Re-export main entry points
pub use types::generate_ast;
pub use syntax::parser::{generate_lalrpop_grammar, write_grammar_file};
pub use term_ops::subst::generate_substitution;
pub use runtime::language::generate_language_impl;
pub use runtime::metadata::generate_metadata;

// Shared helper functions (from current mod.rs)
pub fn is_var_rule(rule: &GrammarRule) -> bool { ... }
pub fn is_integer_rule(rule: &GrammarRule) -> bool { ... }
pub fn generate_var_label(category: &Ident) -> Ident { ... }
pub fn generate_literal_label(native_type: &syn::Type) -> Ident { ... }
```

### Phase 8: Delete empty `ast_gen.rs`
After extraction, `ast_gen.rs` should be empty and can be deleted.

---

## Future Improvements (Not Required Now)

### Large File Splitting

Some files are very large and could be split further if needed:

**`gen/syntax/parser/lalrpop.rs` (1802 lines)**
Could split into:
- `tokens.rs` - Lexer/token generation
- `rules.rs` - Rule analysis and pattern matching
- `actions.rs` - Action code generation
- `lalrpop.rs` - Entry point and orchestration

**`gen/term_ops/subst.rs` (1638 lines)**
Could split into:
- `variants.rs` - VariantKind analysis
- `capture_avoiding.rs` - Main capture-avoiding substitution
- `env_subst.rs` - Environment-based substitution
- `unify.rs` - FreeVar unification

These splits are optional and can be done later if the files become difficult to navigate.

---

## Open Questions

1. **Where should `env.rs` go?** Currently generates `{Name}Env` types for REPL bindings.
   - Option A: `gen/runtime/env.rs` (runtime support)
   - Option B: `gen/term_ops/env.rs` (used by substitution)
   - Recommendation: `gen/runtime/` since it's for REPL variable storage

2. **Shared helper functions location?**
   - `is_var_rule()`, `is_integer_rule()`, `generate_var_label()`, etc.
   - Option A: `gen/mod.rs`
   - Option B: `utils.rs` (crate-wide)
   - Recommendation: Keep in `gen/mod.rs` since they're codegen-specific

---

## Benefits

1. **Clarity** - Each module has a single, clear purpose
2. **Discoverability** - Related code is co-located
3. **Maintainability** - Smaller, focused files
4. **Extensibility** - `native/` ready for expansion, clear places for new features
5. **Testability** - Each module can be tested independently

## Trade-offs

1. **More files** - ~6-8 new files from splitting
2. **Import changes** - All existing imports need updating
3. **Refactoring risk** - Need careful testing during migration
