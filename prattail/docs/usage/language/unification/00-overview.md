# Language Unification Guide

**Updated:** 2026-03-03

## Motivation

Real-world language tooling rarely operates on a single, monolithic grammar.
Domain-specific extensions, embedded DSLs, and modular operator libraries all
demand the ability to compose grammars from independently defined pieces.
PraTTaIL supports this through five complementary mechanisms that span two
architectural levels:

1. **Modularity** -- Define operator sets, literal patterns, or semantic rules
   once and reuse them across languages without copy-paste.
2. **Extensibility** -- Build language families where a child language inherits
   and extends a parent's syntax and semantics.
3. **Late Binding** -- Compose languages at runtime where each sub-language
   retains its own parser, enabling independent evolution and version pinning.
4. **Tooling Integration** -- Programmatically compose `LanguageSpec` values
   from analysis tools, IDEs, or build systems without touching macro DSL code.

This guide covers all five mechanisms, when to use each, and how they interact
with the WFST-informed pipeline (dead-rule detection, prediction weights, lint
layer, and codegen).

---

## Taxonomy of Composition Mechanisms

The five mechanisms fall into two architectural families: **merge-based**
(producing a single unified parser) and **delegation-based** (coordinating
multiple independent parsers).

```
  ┌─────────────────────────────────────────────────────────────────┐
  │                   Grammar Composition                           │
  │                                                                 │
  │  ┌──────────────────────────────────────┐  ┌────────────────┐  │
  │  │     Merge-Based (single parser)      │  │  Delegation    │  │
  │  │                                      │  │  (N parsers)   │  │
  │  │  ┌────────────────────────────────┐  │  │                │  │
  │  │  │ LanguageDef-level (AST merge)  │  │  │ compose_       │  │
  │  │  │                                │  │  │ languages!     │  │
  │  │  │  extends:    full inheritance  │  │  │                │  │
  │  │  │  includes:   grammar-only      │  │  │ Generated      │  │
  │  │  │  mixins:     fragment import   │  │  │ delegation     │  │
  │  │  └────────────────────────────────┘  │  │ wrapper        │  │
  │  │                                      │  │                │  │
  │  │  ┌────────────────────────────────┐  │  └────────────────┘  │
  │  │  │ LanguageSpec-level (API merge) │  │                      │
  │  │  │                                │  │                      │
  │  │  │  compose_languages()           │  │                      │
  │  │  │  compose_many()                │  │                      │
  │  │  │  compose_with_wfst()           │  │                      │
  │  │  └────────────────────────────────┘  │                      │
  │  └──────────────────────────────────────┘                      │
  └─────────────────────────────────────────────────────────────────┘
```

**Merge-based** mechanisms combine grammar fragments into a single
`LanguageDef` or `LanguageSpec` before the pipeline runs.  The result is one
lexer, one parser, one set of FIRST/FOLLOW sets, and one WFST prediction model.
Ambiguities between the merged fragments are resolved at compile time by the
pipeline's four-tier dead-rule detection and the lint layer.

**Delegation-based** mechanisms leave each sub-language's parser intact and
generate a thin wrapper that dispatches input to the appropriate sub-parser at
runtime.  This is the right choice when the sub-languages are independently
versioned, when their grammars would conflict if merged, or when you need
runtime language selection.

---

## Comparison Table

| Mechanism | Level | What Merges | Duplicate Strategy | Generates Parser? | When to Use |
|-----------|-------|-------------|--------------------|--------------------|-------------|
| `extends:` | LanguageDef | types+terms+eqs+rw+logic | Error | Yes (merged) | Language families, additive extensions |
| `includes:` | LanguageDef | types+terms only | Override | Yes (merged) | Import syntax, provide own semantics |
| `mixins:` | LanguageDef | types+terms only | Override | Yes (merged) | Reusable operator sets from fragments |
| `compose_languages!` | Delegation | None | N/A | No (per-sub-lang) | Independent languages, late binding |
| `compose_languages()` | LanguageSpec | types+terms | Error | Yes (merged) | Programmatic/tooling composition |

Key distinctions:

- **Duplicate Strategy: Error** means the merge aborts with a compile-time
  error if both sides define a type or term with the same name.  This is
  appropriate for `extends:` and `compose_languages()` because the user
  explicitly intends additive composition and duplicates signal a design
  mistake.

- **Duplicate Strategy: Override** means the importing side's definition wins.
  This is appropriate for `includes:` and `mixins:` because the user is
  cherry-picking syntax from an existing grammar and may intentionally redefine
  certain constructs.

---

## Decision Flowchart

Use this flowchart to choose the right mechanism for your use case:

```
  Start: Do you need a single unified parser?
    │
    ├── Yes ──> Do you want full semantic inheritance?
    │           │
    │           ├── Yes ──> extends:
    │           │
    │           └── No ──> Do you have fragments to import?
    │                       │
    │                       ├── Yes ──> mixins:
    │                       │
    │                       └── No ──> Do you need the base's equations/rewrites?
    │                                   │
    │                                   ├── No ──> includes:
    │                                   │
    │                                   └── Yes ──> extends:
    │
    └── No ──> compose_languages!
```

**Quick rules of thumb:**

- If you are building a language family (e.g., "Core" -> "Extended" ->
  "Full"), use `extends:`.
- If you want to borrow syntax from another language but supply your own
  reduction rules, use `includes:`.
- If you have a library of reusable operator fragments (e.g., arithmetic, logic,
  comparison), use `mixins:`.
- If the sub-languages are independent and you want runtime dispatch, use
  `compose_languages!`.
- If you are a tool author composing `LanguageSpec` values programmatically, use
  `compose_languages()` or `compose_many()`.

---

## End-to-End Pipeline

The diagram below traces how composition hooks feed into the full validation,
pipeline, and codegen chain.  Every merge-based mechanism converges at the
"Merged LanguageDef" stage; from there the path is identical regardless of
which mechanism produced it.

```
  language! { extends: [Base], mixins: [Frag], ... }
      │
      ▼
  macros crate: parse DSL ──> LanguageDef
      │
      ├── apply_extends()     ─── merge_language_defs(base, ext, Error)
      ├── apply_includes()    ─── merge_language_defs(base, ext, Override)
      ├── apply_mixins()      ─── merge_language_defs(base, ext, Override)
      │
      ▼
  Merged LanguageDef
      │
      ▼
  project_to_language_spec() ──> LanguageSpec
      │
      ▼
  run_pipeline()
      │
      ├── Extract   ──> LexerBundle + ParserBundle
      ├── Generate  ──> lexer_code + parser_code
      │    ├── FIRST/FOLLOW sets
      │    ├── WFST prediction
      │    ├── Dead-rule detection (four-tier)
      │    ├── Lint layer (23 lints)
      │    └── Codegen
      ├── Finalize  ──> TokenStream
      │
      ▼
  Generated parser (merged grammar)
```

For `compose_languages!`, the pipeline runs independently for each sub-language
and the delegation wrapper is generated separately by the compose codegen pass.

---

## Quick Example

A concrete example to illustrate the most common pattern -- extending a base
language with new operators:

```rust
// Base language: arithmetic over integers
language! {
    name: Arith,
    types { Int, Bool }
    terms {
        rule Add: Int = Int "+" Int;
        rule Mul: Int = Int "*" Int;
        rule Lit: Int = r"[0-9]+";
    }
}

// Extended language: adds comparison operators
language! {
    name: ArithCmp,
    extends: [Arith],
    terms {
        rule Eq:  Bool = Int "==" Int;
        rule Neq: Bool = Int "!=" Int;
        rule Lt:  Bool = Int "<"  Int;
        rule Gt:  Bool = Int ">"  Int;
    }
}
```

`ArithCmp` inherits all of `Arith`'s types, terms, equations, rewrites, and
logic blocks.  The pipeline sees one merged grammar with six term rules and two
types.  WFST prediction weights cover the full merged grammar, and dead-rule
detection operates across both the inherited and locally defined rules.

---

## Sub-Documents

Each mechanism is covered in depth in its own sub-document:

| Document | Title | Description |
|----------|-------|-------------|
| [01-extends.md](01-extends.md) | `extends:` -- Full Inheritance | Inheriting types, terms, equations, rewrites, and logic from a base language. Error-on-duplicate semantics. |
| [02-includes.md](02-includes.md) | `includes:` -- Grammar-Only Import | Importing types and terms without inheriting semantic rules. Override-on-duplicate semantics. |
| [03-mixins.md](03-mixins.md) | `mixins:` -- Fragment Import | Composing reusable operator fragments defined with `language_fragment!`. |
| [04-compose.md](04-compose.md) | `compose_languages!` -- Delegation | Runtime dispatch across independently compiled sub-language parsers. |
| [05-spec-level-composition.md](05-spec-level-composition.md) | `compose_languages()` API | Programmatic `LanguageSpec`-level composition for tooling and IDE integration. |
| [06-cross-category.md](06-cross-category.md) | Cross-Category Dispatch | Implicit unification via FIRST set overlap analysis and WFST-weighted dispatch. |
| [07-cast-rules.md](07-cast-rules.md) | Category Embeddings | Cast rules for type coercion, reachability graphs, and dead-rule interaction. |
| [08-best-practices.md](08-best-practices.md) | Best Practices | Decision tree, anti-patterns, performance considerations, migration guide. |

---

## Source Reference

| Purpose | File |
|---------|------|
| Merge semantics | `macros/src/ast/merge.rs` |
| Fragment definition | `macros/src/ast/language.rs` |
| Compose codegen | `macros/src/gen/compose_gen.rs` |
| LanguageSpec composition | `prattail/src/compose.rs` |
| Pipeline | `prattail/src/pipeline.rs` |
| WFST prediction | `prattail/src/wfst.rs` |
