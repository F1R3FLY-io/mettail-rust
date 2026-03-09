# Congruence Rule Generation

**Source**: [`macros/src/logic/congruence.rs`](../../src/logic/congruence.rs)

## 1. Overview / Purpose

The congruence module generates explicit rewrite congruence rules declared
in user grammars. These rules propagate rewrites through constructors:
if a subterm rewrites, the enclosing constructor rewrites too.

**Critical distinction**: Rewrite congruences are NOT auto-generated. Users
explicitly control where rewrites propagate (e.g., rewrites through PPar
but not POutput). Equality congruences ARE auto-generated in `equations.rs`
since `eq(x,y) => eq(f(x), f(y))` is always sound.

The module classifies each congruence rule into one of three strategies
(Simple, Collection, Binding), generates the appropriate Ascent code, and
consolidates Simple congruences by field category for reduced code size.

## 2. Architecture and Data Flow

```
 LanguageDef.rewrites
     |
     v
 generate_all_explicit_congruences(language, cat_filter, emit_diagnostics)
     |
     +---> For each rewrite where is_congruence_rule():
     |         |
     |         v
     |     classify_and_generate_congruence(rewrite, language, &mut simple_groups)
     |         |
     |         +---> find_rewrite_context(pattern, source_var, language)
     |         |         |
     |         |         v
     |         |     RewriteContext::Collection  --> generate_collection_congruence()
     |         |     RewriteContext::Binding     --> generate_binding_congruence()
     |         |     RewriteContext::Simple      --> collected into simple_groups
     |         |
     |         v
     |     TokenStream (Collection/Binding) or None (Simple, deferred)
     |
     +---> For each (src_cat, fld_cat) group in simple_groups:
     |         |
     |         v
     |     generate_consolidated_simple_congruence(source_cat, field_cat, entries)
     |         |
     |         +---> Build TLS pool arms for field extraction
     |         +---> Build rebuild match arms for constructor reconstruction
     |         +---> ART04: Build BloomFilter and matches!() guard
     |         |
     |         v
     |     TokenStream (consolidated rule with N match arms)
     |
     +---> Emit G38 diagnostic (ART04 guard summary)
     |
     v
 Vec<TokenStream>
```

## 3. Key Types and Functions

### `RewriteContext` (internal enum)

```rust
enum RewriteContext {
    Collection {
        category: Ident,
        constructor: Ident,
        element_category: Ident,
        has_rest: bool,
    },
    Binding {
        category: Ident,
        constructor: Ident,
        field_idx: usize,
        body_category: Ident,
    },
    Simple {
        category: Ident,
        constructor: Ident,
        field_idx: usize,
        field_category: Ident,
    },
}
```

### `SimpleCongruenceEntry` (internal struct)

```rust
struct SimpleCongruenceEntry {
    constructor: Ident,
    field_idx: usize,
    n_fields: usize,
    is_boxed: bool,
}
```

### Public API

| Function                            | Returns             | Purpose                          |
|-------------------------------------|---------------------|----------------------------------|
| `generate_all_explicit_congruences` | `Vec<TokenStream>`  | Generate all explicit congruence rules |

### Internal Functions

| Function                                    | Purpose                                          |
|---------------------------------------------|--------------------------------------------------|
| `classify_and_generate_congruence`          | Classify and generate/collect a congruence rule   |
| `find_rewrite_context`                      | Determine where the rewrite variable appears      |
| `find_rewrite_context_in_term`              | Recursive context search in PatternTerm           |
| `pattern_contains_var`                      | Check if a pattern references a variable          |
| `generate_collection_congruence`            | Generate collection element rewrite propagation   |
| `generate_binding_congruence`               | Generate binder body rewrite propagation          |
| `generate_consolidated_simple_congruence`   | Generate consolidated simple field congruence     |
| `field_is_boxed_in_ast`                     | Check if a field is stored as Box<T>              |
| `get_binder_body_category`                  | Get body type for a binder at given index         |

## 4. Algorithm Description

### Classification

Each congruence rewrite has the form `| S ~> T |- C(... S ...) ~> C(... T ...)`.
The classifier examines the LHS pattern to determine where `S` appears:

```
classify_and_generate_congruence(rewrite, language, simple_groups):
    (source_var, target_var) = rewrite.congruence_premise()
    context = find_rewrite_context(rewrite.left, source_var, language)

    match context:
        Collection { category, constructor, element_category, has_rest }:
            return generate_collection_congruence(...)
        Binding { category, constructor, field_idx, body_category }:
            return generate_binding_congruence(...)
        Simple { category, constructor, field_idx, field_category }:
            // Defer: collect for consolidation
            simple_groups[(category, field_category)].push(entry)
            return None
```

### Simple Congruence Consolidation

Multiple constructors with the same `(source_cat, field_cat)` pair are
consolidated into a single Ascent rule with inline match expressions:

```
Before consolidation (N rules, one per constructor x field):
    rw_proc(lhs, Proc::PDrop(t)) <-- proc(lhs), if let Proc::PDrop(f0) = lhs,
        rw_name(f0.clone(), t);
    rw_proc(lhs, Proc::POutput(f0, t, f2)) <-- proc(lhs),
        if let Proc::POutput(f0, f1, f2) = lhs, rw_name(f1.clone(), t);

After consolidation (1 rule with N match arms):
    rw_proc(lhs.clone(), rebuild(lhs, vi, t)) <--
        proc(lhs),
        if matches!(lhs, Proc::PDrop(..) | Proc::POutput(..)),  // ART04
        for (field_val, vi) in TLS_POOL.extract(lhs),
        rw_name(field_val, t);
```

### TLS Pool Pattern

The consolidated rule uses a thread-local Vec pool for zero-allocation
iteration (from `common::generate_tls_pool_iter`):

```
Extraction pool arms:
    Proc::PDrop(x0)         => { buf.push(((*x0).clone(), 0)); }
    Proc::POutput(_, x1, _) => { buf.push(((*x1).clone(), 1)); }
    _                       => {}

Rebuild match arms:
    (Proc::PDrop(_), 0)           => Proc::PDrop(Box::new(t.clone()))
    (Proc::POutput(x0, _, x2), 1) => Proc::POutput(x0.clone(), Box::new(t.clone()), x2.clone())
    _                             => unreachable!()
```

### Collection Congruence

For collection constructors like `PPar {S, ...rest}`:

```
rw_proc(parent.clone(), result) <--
    proc(parent),
    if let Proc::PPar(ref bag) = parent,
    for (elem, _count) in bag.iter(),
    rw_proc(elem.clone(), elem_rewritten),
    let result = Proc::PPar({
        let mut new_bag = bag.clone();
        new_bag.remove(elem);
        Proc::insert_into_ppar(&mut new_bag, elem_rewritten.clone());
        new_bag
    });
```

The rule iterates over all elements of the collection bag, rewrites each one
that has a rewrite, and reconstructs the collection with the rewritten element.

### Binding Congruence

For binding constructors like `PNew x S`:

```
rw_proc(lhs.clone(), rhs) <--
    proc(lhs),
    if let Proc::PNew(ref scope) = lhs,
    let binder = scope.unsafe_pattern().clone(),
    let body = scope.unsafe_body(),
    rw_proc((**body).clone(), body_rewritten),
    let rhs = Proc::PNew(
        mettail_runtime::Scope::from_parts_unsafe(binder.clone(), Box::new(body_rewritten.clone()))
    );
```

Note the use of `unsafe_pattern()` and `unsafe_body()` to access scope
internals without opening/re-binding (which would change the binder identity
and potentially cause infinite loops in the fixpoint).

### ART04 Bloom Filter Integration

For consolidated simple congruence, a bloom filter verifies the constructor set:

```
1. Build BloomFilter from participating constructor labels
2. debug_assert! all labels pass might_contain_str (zero false negatives)
3. Generate matches!() guard from the known set
4. Emit G38 diagnostic with guard count
```

## 5. Generated Code Patterns

### Simple (consolidated) -- 2 constructors, 1 field category:

```rust
rw_proc(lhs.clone(), match (lhs, vi) {
    (Proc::PDrop(_), 0) => Proc::PDrop(Box::new(t.clone())),
    (Proc::POutput(x0, _, x2), 1) => Proc::POutput(x0.clone(), Box::new(t.clone()), x2.clone()),
    _ => unreachable!(),
}) <--
    proc(lhs),
    if matches!(lhs, Proc::PDrop(..) | Proc::POutput(..)),
    for (field_val, vi) in {
        thread_local! {
            static POOL_PROC_SCONG_NAME: std::cell::Cell<Vec<(Name, usize)>> =
                const { std::cell::Cell::new(Vec::new()) };
        }
        let mut buf = POOL_PROC_SCONG_NAME.with(|p| p.take());
        buf.clear();
        match lhs {
            Proc::PDrop(x0) => { buf.push(((*x0).clone(), 0)); },
            Proc::POutput(_, x1, _) => { buf.push(((*x1).clone(), 1)); },
            _ => {},
        }
        let iter_buf = std::mem::take(&mut buf);
        POOL_PROC_SCONG_NAME.with(|p| p.set(buf));
        iter_buf
    }.into_iter(),
    rw_name(field_val, t);
```

### Collection -- bag element rewrite:

```rust
rw_proc(parent.clone(), result) <--
    proc(parent),
    if let Proc::PPar(ref bag) = parent,
    for (elem, _count) in bag.iter(),
    rw_proc(elem.clone(), elem_rewritten),
    let result = Proc::PPar({ /* bag clone, remove, insert */ });
```

### Binding -- scope body rewrite:

```rust
rw_proc(lhs.clone(), rhs) <--
    proc(lhs),
    if let Proc::PNew(ref scope) = lhs,
    let binder = scope.unsafe_pattern().clone(),
    let body = scope.unsafe_body(),
    rw_proc((**body).clone(), body_rewritten),
    let rhs = Proc::PNew(Scope::from_parts_unsafe(binder.clone(), Box::new(body_rewritten.clone())));
```

## 6. Integration with Pipeline

Called from `mod.rs::generate_rewrite_rules()` which is invoked from
`generate_ascent_source()`:

```rust
let congruence_rules = congruence::generate_all_explicit_congruences(
    language, cat_filter, emit_diagnostics,
);
```

The `emit_diagnostics` flag is `true` for the main struct and `false` for
the core struct (avoiding duplicate diagnostics in SCC splitting).

The resulting `TokenStream` rules are appended to the rewrite rules section
of the generated Ascent content.

### Demand-Driven Filtering (ART06)

Categories not in the demanded set are skipped via `in_cat_filter()`. The
category filter is applied at the top of `generate_all_explicit_congruences()`.

## 7. Diagnostic Emissions

| Lint ID | Name                               | Severity | Trigger                           |
|---------|------------------------------------|----------|-----------------------------------|
| G38     | `bloom-filter-rw-congruence-guard` | Note     | Rewrite congruence groups guarded by discriminant pre-check |

The G38 diagnostic includes:
- Number of guarded rewrite congruence groups
- Total participating constructor count
- Hint explaining the ART04 optimization

## 8. Test Coverage

The congruence module is tested through integration tests that compile
full language definitions with explicit congruence rules:

- **RhoCalc tests**: Exercise all three congruence strategies (Simple for
  POutput fields, Collection for PPar bag elements, Binding for PNew scope)
- **Lambda tests**: Exercise binding congruence
- **Ambient tests**: Exercise collection congruence

No standalone unit tests exist in `congruence.rs` itself; coverage is
achieved through the end-to-end compilation pipeline.

## 9. Source References

- **Primary source**: [`macros/src/logic/congruence.rs`](../../src/logic/congruence.rs) (~722 lines)
- **TLS pool generation**: [`macros/src/logic/common.rs`](../../src/logic/common.rs), `generate_tls_pool_iter()`
- **Bloom filter**: [`macros/src/logic/bloom_filter.rs`](../../src/logic/bloom_filter.rs)
- **Invocation**: [`macros/src/logic/mod.rs`](../../src/logic/mod.rs), via `generate_rewrite_rules()`

## 10. Cross-References

- [bloom-filter.md](bloom-filter.md) -- ART04 pre-check used in consolidated simple congruence
- [equation-system.md](equation-system.md) -- equality congruences (auto-generated, different from rewrite congruences here)
- [rule-generation.md](rule-generation.md) -- unified rule clause generation shared with rewrite rules
- [rule-fusion.md](rule-fusion.md) -- congruence rules are explicitly excluded from BCG02 fusion
- [`docs/design/codegen-optimization-catalog.md`](../../../docs/design/codegen-optimization-catalog.md) -- ART04 catalog entry
