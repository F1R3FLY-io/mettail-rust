# Ground Term Identification

## Overview

The ground detection module generates per-category `is_ground()` methods that
recursively determine whether a term contains any free variables. A **ground
term** is fully concrete: every leaf position is occupied by a literal value or
a nullary constructor, never a variable. Bound variables inside `Scope` bindings
do not make a term non-ground, because they are locally bound and do not
represent unresolved references.

**Source:** `macros/src/gen/term_ops/ground.rs`

## Motivation

The previous `is_accepting()` implementation had two deficiencies:

1. **Wasteful for native types:** It called `try_eval()` to compute the full
   native value, then discarded it -- only to re-evaluate later. `is_ground()`
   performs zero arithmetic.

2. **Shallow for compound types:** It only checked for bare variables at the
   top level, missing variables nested inside compound terms (e.g.,
   `PSend(NVar(x), PZero)` was incorrectly reported as ground). `is_ground()`
   performs a deep recursive traversal.

## Algorithm Description

The detection follows a top-down structural recursion. Each variant maps to a
boolean expression:

| Variant Kind | Result | Rationale |
|--------------|--------|-----------|
| `Var` | `false` | Variables are by definition non-ground |
| `Literal` | `true` | Literals contain no variables |
| `Nullary` | `true` | Nullary constructors contain no variables |
| `Regular` | `f0.is_ground() && f1.is_ground() && ...` | All fields must be ground |
| `Collection` | `coll.iter().all(\|x\| x.is_ground())` | All elements must be ground |
| `Binder` | `f0.is_ground() && ... && scope.body.is_ground()` | Pre-scope fields and body must be ground |
| `MultiBinder` | Same as Binder | Multi-binder handled identically |

The key design choice is that binder bodies are checked via
`scope.inner().unsafe_body.is_ground()` -- this accesses the body without
unbinding (no fresh variable generation), which is both efficient and correct
because `is_ground()` does not need to inspect variable identity.

### Collection Iteration Patterns

Different collection types have different iteration signatures:

| Collection Type | Iterator Yields | Ground Check |
|----------------|----------------|--------------|
| `HashBag` | `(&T, usize)` | `coll.iter().all(\|(x, _count)\| x.is_ground())` |
| `Vec` | `&T` | `coll.iter().all(\|x\| x.is_ground())` |
| `HashSet` | `&T` | `coll.iter().all(\|x\| x.is_ground())` |

## Generated Code Patterns

For each category, the generator emits:

```rust
impl Cat {
    /// Returns `true` if this term contains no free variables.
    pub fn is_ground(&self) -> bool {
        match self {
            // One arm per variant
        }
    }
}
```

### Worked Example

For a rho-calculus language with:
- `Proc::PVar(OrdVar)` -- variable
- `Proc::PZero` -- stopped process
- `Proc::PSend(Box<Name>, Box<Proc>)` -- send
- `Proc::PPar(HashBag<Proc>)` -- parallel composition
- `Proc::PInput(Box<Name>, Scope<Binder<String>, Box<Proc>>)` -- input

The generated code is:

```rust
impl Proc {
    pub fn is_ground(&self) -> bool {
        match self {
            Proc::PVar(_) => false,
            Proc::PZero => true,
            Proc::PSend(f0, f1) => f0.is_ground() && f1.is_ground(),
            Proc::PPar(coll) => coll.iter().all(|(x, _count)| x.is_ground()),
            Proc::PInput(f0, scope) => {
                f0.is_ground() && scope.inner().unsafe_body.is_ground()
            },
        }
    }
}
```

### Ground-check Trace

For the term `PSend(NQuote(PZero), PVar(x))`:

```
PSend(NQuote(PZero), PVar(x))
  +-- f0 = NQuote(PZero)
  |     +-- NQuote is Regular: check PZero.is_ground() = true
  |     +-- result: true
  +-- f1 = PVar(x)
  |     +-- Var: false
  +-- true && false = false    <-- term is NOT ground
```

## Integration with Codegen Pipeline

The ground detection generator is called from `generate_all()`:

```
generate_all()
    --> generate_is_ground_methods(language)
        --> for each category:
            --> collect_category_variants(category, language)
            --> for each variant:
                --> generate_is_ground_arm(category, variant)
```

### BCG04 Ground-LHS Optimization

The `is_ground()` method is used by the BCG04 optimization: when a rewrite
rule's left-hand side is ground, the generated Ascent rule can skip the
variable-matching machinery and directly look up the ground term in the
relation. This converts an O(n) scan to an O(1) hash lookup.

### Acceptance Checking

In the Ascent evaluation loop, `is_ground()` replaces the older
`is_accepting()` method for determining whether a term has reached a terminal
form (i.e., no further reductions are possible because no variables remain
to substitute).

## Key Functions

| Function | Purpose |
|----------|---------|
| `generate_is_ground_methods()` | Entry point: produces `impl` blocks for all categories |
| `generate_is_ground_arm()` | Dispatches to variant-specific arm generators |
| `generate_regular_arm()` | Handles `Regular`: chains `&&` over field checks |
| `generate_binder_arm()` | Handles `Binder`/`MultiBinder`: checks pre-scope fields and body |
| `collection_all_ground()` | Generates `.iter().all(...)` with correct iterator destructuring |
| `field_ground_check()` | Generates check for a single field (scalar or collection) |

## Source References

- Generator: `macros/src/gen/term_ops/ground.rs`
- Variant types: `macros/src/gen/term_ops/subst.rs` (`VariantKind`, `FieldInfo`)
- Pipeline call site: `macros/src/gen/mod.rs` (line 82)
- BCG04 optimization: `prattail/src/cost_benefit.rs`
