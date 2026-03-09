# ART05 -- Term Depth Computation

## Overview

The depth analysis module generates per-category `term_depth()` methods that
recursively compute the maximum nesting depth of a MeTTaIL term. These methods
are used by the ART05 post-fixpoint convergence check to detect unbounded term
growth during Ascent evaluation. If a term's depth exceeds the configured bound,
the fixpoint computation is terminated early to prevent divergence.

**Source:** `macros/src/gen/term_ops/depth.rs`

## Algorithm Description

The depth computation follows a bottom-up structural recursion over the AST.
Each variant maps to a specific depth formula:

| Variant Kind | Depth Formula | Rationale |
|--------------|---------------|-----------|
| `Var` | 0 | Variables are leaves |
| `Literal` | 0 | Literals are leaves |
| `Nullary` | 0 | Zero-argument constructors are leaves |
| `Regular` | 1 + max(field depths) | One constructor layer plus deepest child |
| `Collection` | 1 + max(element depths) | One collection layer plus deepest element |
| `Binder` | 1 + max(pre-scope fields, body) | One binding layer plus deepest component |
| `MultiBinder` | 1 + max(pre-scope fields, body) | Same as Binder |

For `Regular` variants with no fields (which is structurally prevented but
handled defensively), the depth is 0 (same as `Nullary`).

For empty collections, `max(element depths)` evaluates to 0 via `.unwrap_or(0)`,
so an empty collection has depth 1.

## Generated Code Patterns

For each category in the language definition, the generator emits:

```rust
impl Cat {
    /// Compute the maximum nesting depth of this term.
    pub fn term_depth(&self) -> u32 {
        match self {
            // One arm per variant
        }
    }
}
```

### Worked Example

Given a language with:
- `Proc::PPar(HashBag<Proc>)` -- parallel composition (collection)
- `Proc::PSend(Box<Name>, Box<Proc>)` -- send (regular, 2 fields)
- `Proc::PInput(Box<Name>, Scope<Binder<String>, Box<Proc>>)` -- input (binder)
- `Proc::PVar(OrdVar)` -- variable
- `Proc::PZero` -- nullary

The generated code is:

```rust
impl Proc {
    pub fn term_depth(&self) -> u32 {
        match self {
            // Leaves
            Proc::PVar(_) => 0,
            Proc::PZero => 0,

            // Collection: 1 + max of elements
            Proc::PPar(coll) => {
                1 + coll.iter()
                    .map(|(x, _count)| x.term_depth())
                    .max()
                    .unwrap_or(0)
            },

            // Regular: 1 + max of fields
            Proc::PSend(f0, f1) => {
                1 + (f0.term_depth()).max(f1.term_depth())
            },

            // Binder: 1 + max(pre-scope fields, body)
            Proc::PInput(f0, scope) => {
                1 + (f0.term_depth())
                    .max(scope.inner().unsafe_body.term_depth())
            },
        }
    }
}
```

### Depth Trace Example

For the term `PSend(NQuote(PZero), PPar({PVar(x)}))`:

```
PSend(NQuote(PZero), PPar({PVar(x)}))
  |
  +-- f0 = NQuote(PZero)
  |     +-- NQuote: 1 + depth(PZero) = 1 + 0 = 1
  |
  +-- f1 = PPar({PVar(x)})
        +-- PPar: 1 + max(depth(PVar(x))) = 1 + 0 = 1

depth = 1 + max(1, 1) = 2
```

## Integration with Codegen Pipeline

The depth generator is called from `generate_all()` in `macros/src/gen/mod.rs`:

```
generate_all()
    --> generate_term_depth_methods(language)
        --> for each category:
            --> collect_category_variants(category, language)
            --> for each variant:
                --> generate_depth_arm(category, variant)
```

The ART05 optimization gate in `prattail/src/cost_benefit.rs` decides at
compile time whether to emit a post-fixpoint depth check. When enabled, the
generated Ascent code inserts a convergence guard after each fixpoint iteration
that calls `term_depth()` on all newly produced terms and compares against a
configurable depth bound.

## Key Functions

| Function | Purpose |
|----------|---------|
| `generate_term_depth_methods()` | Entry point: produces `impl` blocks for all categories |
| `generate_depth_arm()` | Dispatches to variant-specific arm generators |
| `generate_regular_depth_arm()` | Handles `Regular` variants: chains `.max()` over field depths |
| `generate_binder_depth_arm()` | Handles `Binder`/`MultiBinder`: includes scope body depth |
| `collection_max_depth()` | Generates `.iter().map(...).max().unwrap_or(0)` for collections |
| `field_depth_expr()` | Generates depth expression for a single field (scalar or collection) |

## Source References

- Generator: `macros/src/gen/term_ops/depth.rs`
- Variant types: `macros/src/gen/term_ops/subst.rs` (`VariantKind`, `FieldInfo`)
- Pipeline call site: `macros/src/gen/mod.rs` (line 83)
- ART05 cost-benefit gate: `prattail/src/cost_benefit.rs`
