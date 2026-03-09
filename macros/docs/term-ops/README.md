# Term Operations -- Code Generation Module

## Overview

The `macros/src/gen/term_ops/` module generates per-category methods for
manipulating MeTTaIL terms at the AST level. These methods are emitted as
`impl Cat { ... }` blocks during proc-macro expansion and become part of the
generated language crate.

Term operations sit between the AST type generation (`gen/types/`) and the
Ascent logic generation (`logic/`). The Ascent rewrite rules call the generated
methods (substitution, normalization, ground-checking, depth measurement) as
part of their rule bodies.

## Module Index

| File | Optimization | Purpose |
|------|-------------|---------|
| [`subst.rs`](substitution.md) | -- | Capture-avoiding substitution with binder-aware shadowing |
| [`normalize.rs`](normalization.md) | BCG05 | Collection flattening, beta-reduction, cancellation pair collapse |
| [`ground.rs`](ground-detection.md) | BCG04 | Deep recursive free-variable detection |
| [`depth.rs`](depth-analysis.md) | ART05 | Maximum nesting depth measurement |
| [`hash_consing_analysis.rs`](hash-consing-analysis.md) | ART01 | Recursive field detection for hash-consing applicability |

## Architecture

```
                     LanguageDef
                         |
                  generate_all()          macros/src/gen/mod.rs
                    /    |    \
                   /     |     \
    generate_     /  generate_  \  generate_term_
    substitution/  normalize_   \ depth_methods
         |      functions  |      |
         v          v      v      v
    subst.rs   normalize.rs  depth.rs   ground.rs
         \          |      /      /
          \         |     /      /
           v        v    v      v
         TokenStream (proc_macro2)
                    |
                    v
         Generated impl blocks
         per language category
```

## How Term Operations Feed into Codegen

The `generate_all()` function in `macros/src/gen/mod.rs` calls each term-op
generator and concatenates the resulting `TokenStream` values into the final
output. The call order is:

1. `generate_ast_enums()` -- enum definitions
2. `generate_flatten_helpers()` -- collection flattening (normalize prerequisite)
3. `generate_normalize_functions()` -- `normalize()` methods
4. `generate_substitution()` -- `subst()` / `substitute()` methods
5. `generate_is_ground_methods()` -- `is_ground()` methods
6. `generate_term_depth_methods()` -- `term_depth()` methods

Each generator receives the `LanguageDef` AST and inspects it to determine
which variants exist for each category. The shared `collect_category_variants()`
function (defined in `subst.rs`) produces a unified `Vec<VariantKind>` that
all generators consume, ensuring consistent coverage of every enum variant.

## Variant Classification

All generators share the `VariantKind` enum for classifying AST variants:

```
VariantKind
  +-- Var           Variables (free variables)
  +-- Literal       Native literals (integers, strings, ...)
  +-- Nullary       Zero-argument constructors
  +-- Regular       Constructors with positional fields
  +-- Collection    HashBag / Vec / HashSet constructors
  +-- Binder        Single-variable binding (Scope<Binder<String>, Box<T>>)
  +-- MultiBinder   Multi-variable binding (Scope<Vec<Binder<String>>, Box<T>>)
```

Each generator produces one match arm per variant, ensuring exhaustive
coverage of the generated enum.

## Cross-References

- **Codegen modules**: [Codegen Module Index](../codegen/README.md) -- Ascent Datalog code generation pipeline
- **Runtime types**: [Runtime Module Index](../../../runtime/docs/README.md) -- `OrdVar`, `Scope`, `FreeVar`, `HashBag`, `InternTable`
- ART01 hash-consing analysis connects to
  [`runtime/src/hash_consing.rs`](../../../runtime/docs/hash-consing.md)
- ART05 depth analysis is consumed by the cost-benefit gate in
  `prattail/src/cost_benefit.rs`
- BCG04 ground detection is used by the ground-LHS rewrite optimization
- BCG05 normalization works with the epoch mechanism in
  [`runtime/src/binding.rs`](../../../runtime/docs/binding-infrastructure.md)
- **Diagnostics catalog**: [Diagnostics README](../../../prattail/docs/diagnostics/README.md) -- all lint codes

## Source References

- Module root: `macros/src/gen/term_ops/mod.rs`
- Orchestrator: `macros/src/gen/mod.rs` (lines 56--130)
- Variant classification: `macros/src/gen/term_ops/subst.rs` (`VariantKind`, `FieldInfo`)
