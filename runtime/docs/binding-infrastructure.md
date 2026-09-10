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

### Checked category traversal

`CheckedIterativeBinding::try_copy_iterative` is the fallible category boundary.
It takes the same caller-owned reservation callback as `CheckedBindingLeaf`,
but requires recursive category fields to use an explicit worklist. There is
no blanket `Clone`/`BoundTerm` implementation. `OrdVar` delegates to its checked
leaf operation. The boundary `Arc<T>` adapter reserves one record before either
sharing the existing allocation for Clone or invoking the checked inner worker
and wrapping its result for Open/Close. A refused operation leaves the source
and its sharing unchanged; earlier successful reservations are not refunded.
This adapter must not replace worklist scheduling of nested category fields.

`BindingOperation` keeps the borrowed binder roster with the invocation.
`state()` supplies its initial depth, and `with_state(state)` applies a work
item's inherited depth without copying the roster or changing the operation.
`under_scope()` derives the body operation from the parent: Clone stays Clone;
Open/Close increment once after checking the `u32` boundary. Overflow returns
`ScopeDepthOverflow` before Moniker's unchecked increment. Ordinary fields and
siblings continue with the original parent operation, so descending into one
body cannot change another child's binding depth. These pure helpers do not
reserve work; the enclosing worker admits its transition before using them.

The [inherited-state model](../../formal/rocq/rho_bridge/theories/RholangInheritedBindingFold.v)
proves these depth rules and their composition with the existing structural
fold. The checked-interface tests compare binding coordinates and names,
preserve roster pointer identity, check sibling depth independence, and exercise
Arc sharing, exact/under limits, refusal and retry. A unit test checks the full
`u32` successor boundary directly; it does not fabricate Moniker's private
`ScopeState` representation. These interface tests do not establish a generated
language's traversal or activate its parser actions.

The category worker uses indexed `Option<T>` result cells with the existing
two-vector pool lifecycle. `append_binding_slots` checks the range arithmetic
and reserves initialization work plus cell records before appending empty
cells; existing values retain their order and ownership. `write_binding_slot`
admits one step and checks the supplied value's category, bounds, and empty
destination before filling it. `take_binding_slot` admits one step and checks
bounds, readiness, and category before removing the value. Generated category
checks inspect only the enum discriminant, never syntax or printed names.

These operations distinguish slot-shape errors from reservation failures and
size overflow. A refused operation leaves the cells unchanged. A failed write
drops its incoming value, whose construction and cleanup must already have
been admitted by the producer. Earlier successful takes are not rolled back;
the worker owns and cleans up those partial results. The helpers do not clone
values, allocate a second worklist, or establish pointer validity for the
producer's borrowed source.

The [indexed-slot model](../../formal/rocq/rho_bridge/theories/IndexedCopySlots.v)
proves range disjointness, prefix retention, write/take-once laws, and ordered
extraction of a ready range, including repeated values. Its category tags map
to the generated discriminant checks. The [slot tests](../tests/binding_slots.rs)
use non-Clone values to check these operations, typed refusals, exact/under
admission, overflow, cancellation before validation, and ownership on failure.
The generator still must establish that each assembly's slots are ready and
hold the expected categories.

### Generated replacement cleanup

The generated destructor replaces extracted category fields with selected
dummy values. A closed-data dummy can itself contain a finite tree of category
Arcs; it is not necessarily a leaf. `DummyPlan` in the existing
[Drop emitter](../../macros/src/gen/term_ops/iterative_drop.rs) records exactly
which constructors its productivity analysis selected, preserving dependency
order and repeated fields. Resource projection must reuse the rendering choices;
a resource calculation must not select a different, cheaper dummy.

The [replacement-receipt model](../../formal/rocq/rho_bridge/theories/GeneratedDummyCleanupReservation.v)
separates five event counts for each selected finite recipe:

| Receipt | Meaning |
| --- | --- |
| `construction` | Build the selected dummy and its fresh child Arcs |
| `extraction` | Extract original children and construct their replacements |
| `active_drop` | Destroy a dummy while the iterative destructor's active flag is set |
| `popped_drop` | Process an owned dummy task, its original children and its active replacement shell |
| `normal_drop` | Destroy a root with the active flag clear and an available empty work pool |

This distinction matters because the root's automatic field destruction runs
after the active flag is cleared. Its replacement children require normal
cleanup, whereas replacement children in popped task shells use active
cleanup. The model folds the actual dependency occurrences, including repeats,
and proves that normal-cleanup credit also covers active cleanup under any
nonnegative event weighting. It composes the resulting construction and cleanup
charges with the existing preparation reservation laws; it is not another meter.

Native/default construction and flat field cleanup remain explicit local
contracts. Copying an existing canonical numeric handle does not establish the
cost of constructing its default value. Type names likewise do not establish
that cost. The finite-recipe laws require a concrete descriptor mapping and
source-backed local charges before numerical receipts can be used by generated
code. They do not prove arbitrary shared-AST destruction, allocator capacity,
panic recovery, or thread-local-storage teardown behavior.

### Bag reconstruction during binding

Binding can make previously distinct bag keys equal. The existing
`HashBag::close_term` and `open_term` semantics rebuild those keys with
`HashMap::insert`, not the accumulating `HashBag::insert_n` operation. Their
shared private helper accepts transformed entry/count pairs in visitation
order, keeps the first equal key object and last supplied count, retains the
original `total_count`, and recomputes the cached hash summary once.

`HashBag::rebuild_binding_entries` exposes this same recipe to generated
reconstruction. It does not transform keys itself. Its caller supplies one
transformed pair per original distinct entry, in the original traversal
order. Diagnostic fields ignored by key equality still belong to the first
stored key, so sorting or reversing equal-key entries changes behavior.
Ordinary cloning and accumulating insertion remain unchanged.

For example, if two distinct source entries with counts 2 and 5 transform
into equal keys, the stored count is 5 when that is the visitation order,
while the retained total is 7. Reversing visitation selects count 2 instead.
This documents the existing generic binding behavior; it neither establishes
that such collisions occur in a well-formed freshening workflow nor repairs
the difference between retained total and surviving multiplicities.

The [bag model](../../formal/rocq/rho_bridge/theories/HashBagBindingReconstruction.v)
proves transformation/insertion fusion and the retained-key/count recipe.
It abstracts concrete hashing and map bucket order. Runtime tests compare
the helper and native open/close against the previous insertion loop using
real free/bound-variable collisions, and compare cached hashes with a full
recomputation. The helper is not a checked allocation interface, and the
model makes no panic-unwind recovery claim.

### Checked leaf copies and binding

[`CheckedBindingLeaf`](../src/checked_binding.rs) supplies the payload boundary
for a resource-admitted generated traversal. A leaf receives a clone, open, or
close operation and the caller's reservation callback. It returns an owned
result or a typed refusal; it neither creates another budget nor freshens names.
There is no blanket implementation based on `Clone` or `BoundTerm`, because
either trait can conceal recursive work in a native payload.

| Payload or operation | Admission and behavior |
| --- | --- |
| Fixed scalar or canonical numeric handle | Reserve one copy record; copy the existing value or handle, not a numeric magnitude |
| String or byte vector | Reserve one record and its actual byte length before copying |
| Direct `FreeVar<String>` | Reserve its record and optional name bytes; Moniker binding is a no-op on this type |
| Closing `OrdVar(Var::Free(...))` | Admit inspection and each ordered identity comparison; select the first matching identity, validate its `u32` index, then reserve the copy using the source name |
| Opening a matching-depth bound variable | Admit inspection; validate the roster index; reserve and copy the selected binder's identity and name |
| Other variable cases | Admit inspection and copy the unchanged variable |

A copy record costs one logical work unit and four logical retention units;
each owned byte adds one to each charge. Inspection and each identity comparison
cost one work unit without retained units. Arithmetic is checked before the
callback. These are logical resource units, not physical allocation capacity,
resident memory, or elapsed time. Refusal leaves the source unchanged, but
already admitted work is not refunded. Cancellation is checked during ordered
lookup rather than only at entry.

The [leaf model](../../formal/rocq/rho_bridge/theories/MonikerLeafOperations.v)
proves first-identity selection, name provenance, index bounds, and opening
behavior. Concrete closing correspondence is restricted to representable
indices and depths: legacy Moniker casts the index, whereas this API rejects
overflow. A missing index at matching depth is a typed refusal instead of
Moniker's panic. The model does not prove resource accounting, freshening, or
the complete generated traversal. These leaf implementations alone do not
activate the generated binding worker or establish whole-program stack safety.

For an `FltNode`, the checked copy changes only its selector. Guest text,
structural holes and their order, ranges, declared bounds, and source position
are copied verbatim. No parser or validating constructor runs during copying.
The [FLT composition model](../../formal/rocq/rho_bridge/theories/FltSelectorBinding.v)
lifts the leaf operation through that exact payload-preserving record update.

Payload inspection is admitted before scanning hole and piece entries, with a
cancellation poll at each entry. Copy charges count the actual five retained
strings, hole names and optional categories, and text-piece bytes. Logical
records include the node, five string headers, two vector headers, each hole
or piece, and its string headers. The selector has its separate checked leaf
charge. The payload charge is admitted before any payload cloning; a refusal
after selector copying retains its already consumed charge but returns no FLT.
Declared `bounds` never replace measured lengths. This copy operation does not
establish template validity: the existing validation boundary still owns that.

Behavioral predicates are different: Moniker binding leaves them unchanged,
but their owned syntax can be deeply nested. Their checked leaf implementation
therefore delegates to
[`BehavioralPred::try_clone_with`](../../prattail/src/behavioral_pred.rs), which
uses the existing iterative reconstruction worker. Ordinary clone and variable
substitution use infallible adapters to that same worker; no second copier or
evaluator is introduced.

The dependency-neutral callback receives separate work, logical-record, and
owned-byte components. The runtime converts these through
`reserve_binding_parts` into the caller's existing budget. Admission precedes
task growth, result construction, child-box allocation, argument-vector storage,
and string copies. Argument inspection and copied bytes are charged separately;
each flat payload also prepays its ordinary teardown. Variable substitution
retains the existing shadowing behavior and admits its string comparisons before
performing them.

Normal failure may leave completed child predicates in the result stack. Each
new predicate therefore prepays three cleanup work units and one cleanup
record; each attached child edge prepays twelve cleanup work units and six
cleanup records. These credits cover the existing destructor's dispatches,
worklists and replacement `Top` boxes. Children retain their earlier credit
when attached to a parent. The
[predicate model](../../formal/rocq/rho_bridge/theories/BehavioralFlatCopy.v)
proves flat payload recipes and additive upper credits for these selected
events. Source review connects the counts to the existing destructor; it is
not a compiler-verified proof of Rust execution, physical allocation bounds,
or panic recovery. Cancellation tests must exercise an already copied deep
child, not merely cancellation during descent before any result exists.

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
