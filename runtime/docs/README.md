# MeTTaIL Runtime -- Module Index

The `runtime` crate provides runtime support types and functions for
MeTTaIL-generated code. It is a dependency of every generated `language!`
invocation, providing binding infrastructure, collection types, core traits,
metadata, and hash-consing.

## Module Index

| Module | Source File | Description |
|--------|------------|-------------|
| [Binding Infrastructure](binding-infrastructure.md) | `binding.rs` | `OrdVar`, `Scope`, variable caching, BCG05 epoch mechanism |
| [Hash Consing](hash-consing.md) | `hash_consing.rs` | ART01 epoch-scoped intern tables, `InternTable<T>`, structural sharing |
| Language Traits | `language.rs` | `Term`, `Language`, `AscentResults`, `RelationData`, `TermInfo` traits and types |
| Metadata | `metadata.rs` | `LanguageMetadata`, `TypeDef`, `TermDef`, `EquationDef`, `RewriteDef` for REPL introspection |
| HashBag | `hashbag.rs` | `HashBag<T>` -- associative-commutative multiset collection type |
| Canonical Floats | `canonical_float.rs` | `CanonicalFloat32`, `CanonicalFloat64` -- float wrappers with `Eq`/`Hash`/`Ord` |
| Matchings | `matchings.rs` | `enumerate_matchings()` -- combinatorial search for zip+map correlated rewrites |
| Display Utilities | `lib.rs` | `DisplaySlice` -- comma-separated formatting for slices of `Display` items |

## Key Types Exported

### Core Traits

| Type / Trait | Module | Description |
|-------------|--------|-------------|
| `Term` | `language.rs` | Base trait for all generated AST types: `display_term()`, `substitute()`, `normalize()` |
| `Language` | `language.rs` | Language implementation trait: `parse()`, `run()`, `term_info()`, `categories()` |
| `LanguageMetadata` | `metadata.rs` | REPL metadata: `types()`, `terms()`, `equations()`, `rewrites()`, `logic_rules()` |

### Binding Types

| Type | Module | Description |
|------|--------|-------------|
| `OrdVar` | `binding.rs` | `Var<String>` wrapper with `Hash + Ord` for Ascent relations |
| `Scope<P, T>` | `binding.rs` | Binding scope: `pattern` (binders) + `body` (scoped term) |

### Data Types

| Type | Module | Description |
|------|--------|-------------|
| `HashBag<T>` | `hashbag.rs` | Multiset with `Hash + Eq` elements, used for AC-unification |
| `CanonicalFloat64` | `canonical_float.rs` | `f64` wrapper with total ordering and hash support |
| `CanonicalFloat32` | `canonical_float.rs` | `f32` wrapper with total ordering and hash support |
| `InternTable<T>` | `hash_consing.rs` | Thread-local interning table for structural sharing |
| `AscentResults` | `language.rs` | Rewrite engine output: equivalence classes, rewrites, relations |

### Thread-Local Functions

| Function | Module | Description |
|----------|--------|-------------|
| `get_or_create_var()` | `binding.rs` | Thread-local variable identity cache |
| `bump_bcg05_epoch()` | `binding.rs` | Advance the BCG05 deduplication epoch counter |
| `bcg05_epoch()` | `binding.rs` | Read the current epoch value |
| `bump_intern_epoch()` | `hash_consing.rs` | Advance the ART01 intern table epoch |
| `intern_epoch()` | `hash_consing.rs` | Read the current intern epoch |
| `clear_var_cache()` | `binding.rs` | Reset the variable identity cache |
| `clear_term_eq_cache()` | `binding.rs` | Reset the term equality cache |

## Related Documentation

- [Codegen Modules](../../macros/docs/codegen/README.md) -- how the macros crate generates code that uses these runtime types
- [Term Operations](../../macros/docs/term-ops/README.md) -- generated `subst()`, `normalize()`, `depth()` methods
- [Diagnostics: Ascent Lints](../../prattail/docs/diagnostics/README.md) -- A01--A10, relevant to runtime behavior
