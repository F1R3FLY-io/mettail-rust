# Binding Infrastructure -- OrdVar, Scope, and Moniker Wrappers

## Overview

The binding module provides wrappers around the `moniker` crate's name-binding
types that add `Hash` and `Ord` implementations required by MeTTaIL's Ascent
integration. Ascent relations require `Hash` for their hash-map-based storage,
and term generation/enumeration requires `Ord` for canonical ordering. The
upstream `moniker` crate does not provide these trait implementations because
they are not universally safe for binding-aware types, but MeTTaIL's specific
usage patterns make them sound.

The module also provides thread-local caching infrastructure for variable
identity, term equality, and the BCG05 epoch mechanism.

**Source:** `runtime/src/binding.rs`

## Key Types

### `OrdVar` -- Ordered Variable Wrapper

A `#[repr(transparent)]` newtype around `moniker::Var<String>` that adds
`Ord` and `PartialOrd`.

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct OrdVar(pub Var<String>);
```

**Ordering strategy:**

```
OrdVar(Free(_))  <  OrdVar(Bound(_))     -- Free < Bound by discriminant

OrdVar(Free(a)) vs OrdVar(Free(b)):
    compare hash(a.unique_id) vs hash(b.unique_id)
    -- deterministic within a process (DefaultHasher)
    -- no collisions in practice for u32-sized UniqueId

OrdVar(Bound(a)) vs OrdVar(Bound(b)):
    a.scope.cmp(&b.scope).then(a.binder.cmp(&b.binder))
    -- lexicographic on (ScopeOffset, BinderIndex)
```

The hash-based ordering for `FreeVar` is necessary because `moniker::UniqueId`
does not expose its inner value or derive `Ord`. This ordering is used for
collection ordering and enumeration, not for semantic equality.

**BoundTerm delegation:** `OrdVar` forwards all `BoundTerm<String>` methods
to the inner `Var<String>`:

```rust
impl BoundTerm<String> for OrdVar {
    fn term_eq(&self, other: &Self) -> bool { self.0.term_eq(&other.0) }
    fn close_term(&mut self, ...) { self.0.close_term(...) }
    fn open_term(&mut self, ...) { self.0.open_term(...) }
    fn visit_vars(&self, ...) { self.0.visit_vars(...) }
    fn visit_mut_vars(&mut self, ...) { self.0.visit_mut_vars(...) }
}
```

**Conversions:**
```rust
impl From<Var<String>> for OrdVar { ... }
impl From<OrdVar> for Var<String> { ... }
```

### `Scope<P, T>` -- Hashable/Orderable Scope Wrapper

A wrapper around `moniker::Scope<P, T>` that adds `Hash`, `Ord`, and
`PartialOrd`.

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scope<P, T> {
    inner: moniker::Scope<P, T>,
}
```

**Hash implementation:** Hashes both `unsafe_pattern` and `unsafe_body`
directly, which is safe because `Scope::PartialEq` already compares these
fields alpha-equivalently (the `close_term`/`open_term` operations normalize
bound variable structure).

**Ord implementation:** Zero-allocation comparison using a two-tier strategy:

```
1. Pattern: compare by deterministic hash (no allocation)
   hash_pat(&self.inner.unsafe_pattern).cmp(&hash_pat(&other.inner.unsafe_pattern))

2. Body: compare via T's Ord implementation (tiebreaker)
   .then_with(|| self.inner.unsafe_body.cmp(&other.inner.unsafe_body))
```

**Key methods:**

| Method | Purpose |
|--------|---------|
| `new(pattern, body)` | Create scope by binding a term with a pattern |
| `new_iterative(pattern, body)` | Apply the same closing recipe through `IterativeBinding` |
| `unbind()` | Unbind: freshens bound variables, returns `(P, T)` |
| `unbind2(other)` | Simultaneously unbind two scopes (shared freshening) |
| `inner()` | Access underlying `moniker::Scope` (read-only) |
| `unsafe_pattern()` | Direct pattern access without unbinding |
| `unsafe_body()` | Direct body access without unbinding |
| `from_parts_unsafe(pattern, body)` | Construct without closing (for reconstruction) |

**BoundTerm<String> with cached equality (Sprint B: R1):**

The `BoundTerm<String>` implementation for `Scope` uses `cached_term_eq()`
for the `term_eq()` method, which caches comparison results in a thread-local
`HashMap<(u64, u64), bool>`.

### Iterative closing interface

`IterativeBinding` separates the binding traversal from the scope constructor.
Its `close_iterative` and `open_iterative` methods take a borrowed term, a
Moniker `ScopeState` (the depth at which to bind), and the existing ordered
`Vec<Binder<String>>`. They return a transformed term without changing the
input. Closing selects the first binder with the matching free-variable
identity, not the same printed name. Opening replaces a bound variable only
when its scope offset matches the supplied depth, using its binder index to
select the supplied identity. Neither method freshens names.

Both scope constructors use the same private `with_closing` recipe. Read this
as three ordered operations: extract the pattern's binder vector, close the
body once at depth zero, then retain the unchanged pattern and closed body.
`new` uses the existing `BoundTerm::close_term`; `new_iterative` selects
`IterativeBinding::close_iterative`. Neither constructor treats an unclosed
body as already closed, and neither changes `Scope`'s representation.

```rust
use mettail_runtime::{Binder, FreeVar, OrdVar, Scope, Var};

let name = FreeVar::fresh_named("x".to_owned());
let scope = Scope::new_iterative(
    Binder(name.clone()),
    OrdVar(Var::Free(name)),
);
// The stored body now refers to binder 0 at scope depth 0.
assert!(matches!(scope.unsafe_body().0, Var::Bound(_)));
```

The runtime provides a real `OrdVar` leaf implementation that delegates to
Moniker's existing variable operations. Its `Arc<T>` adapter invokes the inner
implementation and wraps the result in a new `Arc`, leaving any shared input
unchanged. This does not alter ordinary `Arc::clone` sharing. A generated
category implementation must visit recursive children using an explicit
work stack; recursively delegating those children to `BoundTerm` does not
satisfy that contract. The interface and leaf adapters alone do not establish
stack safety for a generated language, and they do not switch parser actions.

These are infallible binding interfaces, not public resource-admission APIs.
As with Moniker, a bound variable at the selected depth must have a valid
binder index; an invalid index panics. Bounded public preparation must use
checked admission and traversal, rather than assuming the constructor reserves
its work. `Scope::unbind`, freshening, alpha equality, and ordinary variable
visitors retain their existing implementations.

The [scope-construction model](../../formal/rocq/rho_bridge/theories/RholangScopeConstructionRecipe.v)
proves the shared recipe's pattern retention, single zero-depth closing
dispatch, and result equality **if** the selected closers agree. This exposes
the generated traversal's correspondence obligation; it does not discharge
it or prove allocation behavior, arbitrary callback effects, or Rust memory
safety. The [integration tests](../tests/iterative_binding.rs) compare actual
stored coordinates, identities, and diagnostic names against Moniker, without
using cached scope equality. They also cover duplicate and reordered binders,
unnamed and Unicode names, nonzero depths, unchanged shared inputs, and the
existing invalid-index refusal behavior.

## Thread-Local Caches

### Variable Cache (`VAR_CACHE`)

```rust
thread_local! {
    static VAR_CACHE: RefCell<HashMap<String, FreeVar<String>>> =
        RefCell::new(HashMap::new());
}
```

Ensures that the same variable name always maps to the same `FreeVar` instance
within a parsing session. This is critical for correct variable identity in
alpha-equivalence checking.

| Function | Purpose |
|----------|---------|
| `get_or_create_var(name)` | Get cached `FreeVar` or create fresh one |
| `get_or_insert_var(var)` | Use existing `FreeVar` if not in cache |
| `clear_var_cache()` | Clear before parsing a new term |
| `var_cache_size()` | Current cache size |

### Term Equality Cache (`TERM_EQ_CACHE`)

```rust
thread_local! {
    static TERM_EQ_CACHE: Cell<HashMap<(u64, u64), bool>> =
        Cell::new(HashMap::new());
}
```

Caches `Scope::term_eq()` results, keyed by structural hash pairs. Keys are
canonicalized (smaller hash first) so that `term_eq(a, b)` and `term_eq(b, a)`
share the same entry.

Uses the `Cell<HashMap>` take/set pattern for zero-overhead thread-local
access (no `RefCell` borrow tracking).

**Collision probability:** For N distinct terms, approximately N^2 / 2^64.
For N = 10,000: approximately 5.4 x 10^-12.

| Function | Purpose |
|----------|---------|
| `clear_term_eq_cache()` | Clear at start of each Ascent evaluation |
| `term_eq_cache_size()` | Current cache size |
| `structural_scope_hash()` | Compute 64-bit hash for cache key |
| `cached_term_eq()` | Look up or compute and cache `term_eq()` result |

### BCG05 Epoch Counter

```rust
thread_local! {
    static BCG05_EPOCH: Cell<u64> = const { Cell::new(0) };
}
```

Incremented at the start of each `run_ascent_typed()` invocation. BCG05
normalize-on-insert dedup guards compare their local epoch against this
counter and clear their `HashSet` on mismatch.

| Function | Purpose |
|----------|---------|
| `bump_bcg05_epoch()` | Increment epoch (called at evaluation start) |
| `bcg05_epoch()` | Read current epoch (called by dedup guards) |

## De Bruijn Index Support

The `Scope` wrapper supports De Bruijn-style variable representation through
moniker's `BoundVar` type:

```rust
BoundVar {
    scope: ScopeOffset(n),    // how many scopes outward
    binder: BinderIndex(k),   // which binder at that scope level
    pretty_name: Option<String>,
}
```

The `unsafe_pattern` and `unsafe_body` fields of a `moniker::Scope` store
variables in this De Bruijn representation after `close_term` is applied.
This representation is used directly (without unbinding) in:

- Hash computation (`Hash` impl)
- Ordering comparison (`Ord` impl)
- Term equality caching (structural hash keys)
- Pattern matching in generated Ascent rules

## Integration with Nominal Analysis

The binding infrastructure connects to the nominal analysis module in
`prattail/src/` through the generated term types:

- `FreeVar<String>` provides the name type for alpha-equivalence
- `Scope::unbind()` / `unbind2()` generate fresh variable names for
  safe substitution under binders
- `OrdVar` wraps `Var<String>` so variables can be stored in Ascent relations
- `Scope::from_parts_unsafe()` enables efficient term reconstruction in
  generated rewrite rules without re-closing

## Re-exports

The module re-exports the following from `moniker`:

```rust
pub use moniker::{Binder, BoundPattern, BoundTerm, BoundVar, FreeVar, Var};
```

These are used directly in generated code (e.g., `mettail_runtime::FreeVar<String>`,
`mettail_runtime::Binder`).

## Test Coverage

| Test | Property |
|------|----------|
| `test_get_or_create_var_same_instance` | Same name returns same `FreeVar` |
| `test_get_or_create_var_different_names` | Different names yield different `unique_id` |
| `test_clear_var_cache_resets` | Clear + recreate yields new `FreeVar` |
| `test_var_cache_size` | Size tracking correct |
| `test_get_or_insert_var_preserves_existing` | Existing cached var preserved |
| `test_ordvar_ordering_free_before_bound` | `Free < Bound` ordering |
| `test_ordvar_display` | Display does not panic |
| `test_ordvar_from_var_roundtrip` | `OrdVar::from` / `Var::from` roundtrip |
| `test_scope_hash_consistent_with_eq` | Equal scopes have equal hashes |
| `test_scope_ord_transitivity` | `a < b, b < c` implies `a < c` |
| `prop_var_cache_idempotent` | (proptest) cache idempotent on repeated lookups |
| `test_bump_bcg05_epoch_increments` | Epoch increments by 1 |
| `test_bcg05_epoch_relative_increment` | Two bumps advance by 2 |
| `test_clear_term_eq_cache_and_size` | Cache clear and size tracking |

## Source References

- Binding module: `runtime/src/binding.rs` (783 lines)
- Re-export: `runtime/src/lib.rs` (lines 11--12)
- Hash-consing integration: `runtime/src/hash_consing.rs`
- Generated substitution calls: `macros/src/gen/term_ops/subst.rs`
- Moniker crate: [docs.rs/moniker](https://docs.rs/moniker)
