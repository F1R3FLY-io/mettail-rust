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

Each retained or replacement child Arc's automatic cleanup includes both
wrapper release and a last-strong-owner check. The shared `Counts::ARC_RELEASE`
contract contributes two logical work events and no records or bytes. This
check is distinct from the earlier `Arc::into_inner` check on the extracted
original child; normal and popped cleanup include both, while active cleanup
includes only automatic release. The native Arc-default contract uses the same
two-event expression. Child category cleanup remains a separate contribution.

Native/default construction and flat field cleanup remain explicit local
contracts. Copying an existing canonical numeric handle does not establish the
cost of constructing its default value. Type names likewise do not establish
that cost. The finite-recipe laws require a concrete descriptor mapping and
source-backed local charges before numerical receipts can be used by generated
code. They do not prove arbitrary shared-AST destruction, allocator capacity,
panic recovery, or thread-local-storage teardown behavior.

The runtime's [`binding_receipt`](../src/binding_receipt.rs) module implements
this algebra with fixed-size event vectors and checked `usize` arithmetic.
Its `const` composition operation consumes previously computed child receipts;
it does not recurse, allocate, select defaults, or invoke a budget callback.
Repeated child fields contribute repeatedly. Overflow returns a typed error
instead of a partial or saturated receipt. Event counts remain unweighted;
the generator still must supply the concrete recipe and native contracts.
Tests check exact leaf and repeated-child recurrences, local contributions,
constant evaluation, overflow, and a 20,000-level iterative dependency chain
on a 256 KiB thread stack on 64-bit targets.

#### Native default contracts

`BindingDefaultReceipt` describes construction and cleanup of a freshly created
native default value. It does not describe copying that type or cleaning up an
arbitrary instance. The associated result is fallible so composed receipts can
report overflow. Extraction is a separate generated-field operation.

The generator can infer the actual Rust payload type by passing the selected
unary constructor to `default_local_for`, or a borrowed field projection to
`default_field_local`. These helpers never execute their function arguments or
construct a value. A native type must explicitly implement the contract; a
name ending in `BigInt`, for example, supplies no accounting authority.

The [native contracts](../src/binding_receipt/defaults.rs) use logical events:

| Event | Meaning at a native default boundary |
| --- | --- |
| `NativeWork` | One bounded native construction or cleanup call, not CPU instructions |
| `NativeRecord` | One selected payload record, plus separately retained allocations |
| `OwnedByte` | Separately handled dynamic payload bytes, not allocator capacity |

Scalar defaults have one construction-call event and one payload record. Empty
containers additionally account for their bounded field cleanup, without
constructing elements or invoking element callbacks. Contracts cover the
runtime's concrete deterministic collection carriers, not arbitrary hashers.
Read/write zipper defaults compose an empty PathMap, an empty focus vector,
and their product.

The canonical integer and rational defaults each retain an outer boxed numeric
value in addition to their payload record. Their zero/one digits are inline in
the pinned dependency version; zero `OwnedByte` does not mean no allocation.
The fixed-point default composes the integer default with its scale pair.
These numeric handles are `Copy`, so their default-field receipts do not invent
deallocation work. A native Arc default composes the inner contract with Arc
allocation and final-owner release; its ownership-check event describes Arc's
destructor check, not `Arc::into_inner`.

These local contracts instantiate the finite-recipe model's parameters. They
do not establish concrete generator correspondence until its selected-field
projection is wired and tested, or prove physical-memory bounds.

#### Selected-recipe projection

The [dummy-receipt emitter](../../macros/src/gen/term_ops/dummy_receipts.rs)
accepts the existing `DummyPlan`; it does not select constructors. It assigns
an index to each recipe in dependency order, rejects missing or late children,
and emits a single const-evaluated table. Repeated child fields reference the
same earlier receipt repeatedly. The generated traversal can then look up a
receipt without walking dependencies at run time.

```text
for each selected recipe in dependency order:
    local, children = project the selected constructor and its actual fields
    require every child to have an earlier table index
    table[index] = checked compose(local, table[children in field order])
return table, or the first typed arithmetic error
```

Construction follows the existing dummy renderer, while extraction follows the
existing destructor branch order. In particular, an opaque optional field is
skipped before optional extraction is considered. A primitive-byte collection
literal is not extracted as a collection of category terms. Empty category
collections have no child receipts, but taking their default replacement and
consuming the empty iterator still have local costs.

The empty consuming-iterator boundary contributes three `NativeWork` events
(construction, terminal `next`, cleanup) and one `NativeRecord`. Replacement
default construction is separate. A regular map's additional `into_inner`
call is not charged to a literal map that consumes its wrapper directly.
Native zipper extraction uses the existing carrier projection for direct or
Arc storage, including the emptied owned carrier's cleanup in the Arc case.

This emitter is infrastructure for checked binding generation. Its existence
does not activate checked traversal or complete public preparation accounting.

#### Precomputed charges and partial outputs

[`BindingCharge`](../src/binding_receipt/charge.rs) projects the event counts
into the existing reservation convention. Its private fields hold base work,
logical records and owned bytes; checked constructors reject overflow in both
the components and the final totals. Each owned byte contributes once to work
and once to retention units. Each logical record contributes four retention
units. These units are not semantic `Cost(G)` grades or measured memory.

Category construction, Arc allocation, cleanup-task pushes and obtaining a
cleanup-pool vector header each contribute one base-work unit and one record.
Other control events contribute one base-work unit. `NativeRecord` contributes
only a record, and `OwnedByte` contributes only bytes before final projection.
The existing reservation callback still owns refusal and budget state.

The generated static `BINDING_DUMMY_CHARGES` table contains construction plus
normal-cleanup charges for each selected dummy. Dependency composition and
event weighting occur during constant evaluation; a traversal can borrow the
table and copy one three-component charge. Both event-count overflow and final
charge overflow remain errors. A dummy charge excludes its enclosing
replacement Arc and is **not** the cost of an arbitrary term in that category.

Actual outputs use the separate
[partial-output model](../../formal/rocq/rho_bridge/theories/GeneratedBindingOutputReservation.v).
Each producer pays its own construction and local cleanup, including required
replacement dummies. Its owned children retain their already-paid allowances.
The additive fold proves that cleanup of independently disposed partial roots
is covered by those allowances, and that assembling a parent transfers child
allowances without paying for the same children again. A popped shell is
bounded by the independently rooted case.

```text
before constructing a parent:
    reserve the parent's own construction and local cleanup allowance
    transfer admitted child outputs from result slots into the parent
on normal refusal:
    dispose the remaining slots, assembly locals and constructed parents
    each owned output occurrence consumes its existing cleanup allowance
```

A shallow Arc into the still-borrowed source has no owned-subtree allowance:
the source owner remains alive during normal-error cleanup. Its local reference
and replacement operations still require admission. Collection collisions must
partition individual owned outputs, not deduplicate equal terms. A map can
retain the first key and last value from different input entries; its discarded
keys and values require their own existing allowances.

The model's partition theorem requires an occurrence-preserving partition,
and its local facts require correspondence to each emitted field branch.
Neither premise follows merely from having a charge table. These laws do not
yet establish the complete generated traversal, concrete collection insertion
costs, panic recovery, or physical allocation bounds.

#### Scalar category fields

The checked emitter handles required `Arc<Category>` and optional
`Option<Arc<Category>>` fields through the existing task and result-slot
machine. Clone preserves shallow sharing with the borrowed source. Open and
Close visit each present child with the parent's inherited binding state;
crossing a scalar field does not introduce a lexical scope. Slots follow source
field order, while visits are pushed in reverse order onto the task stack.

The [scalar-field model](../../formal/rocq/rho_bridge/theories/ScalarArcBindingReservation.v)
instantiates the partial-output algebra with these local charges:

| Field | Clone: work / records | Open or Close: work / records |
| --- | --- | --- |
| Required Arc | 6 / 2, plus selected dummy charge | 7 / 3, plus selected dummy charge |
| Optional, present | 7 / 3 | 8 / 4 |
| Optional, absent | 5 / 2 | 5 / 2 |

These exclude the parent's six-work/two-record base, task and slot transitions,
and already-admitted child outputs. Only a required field constructs a selected
replacement dummy; optional extraction leaves `None`. The source-pinned Clone
premise applies during normal-error cleanup, not after arbitrary later owner
destruction. It is not a bound on an arbitrary shared subtree's lifetime.

Assembly first admits every local charge, then takes **all** child results into
bare category locals. Only after every take succeeds does it construct the
Arc wrappers and parent, with no intervening fallible callback. A failed take
therefore disposes credited bare children; failed publication disposes a fully
admitted parent. The generated-code fixture checks sharing, cross-category
fields, optional presence, variable binding, every small-case refusal boundary,
and a 20,000-level chain on a 256 KiB stack. Checked generation remains inactive
in production until the remaining field families and scope shapes are integrated.

#### Mixed category and native fields

Token text, captured FLT payloads and behavioral predicates are native leaves,
not category children. The checked emitter identifies these fields before
reading their placeholder category metadata. Only actual category children
receive result slots or scheduled visits. Assembly retains a pointer into the
immutably borrowed source so it can copy native fields through their existing
`CheckedBindingLeaf` implementations.

Native copies enter admitted locals before any category result is taken. All
category takes then complete before their Arc wrappers and the parent are
constructed. A later refusal disposes both the admitted native locals and bare
category values; no native payload is hidden inside a pending task.

`Arc<FltNode>` has an explicit leaf adapter: Clone shares the source-pinned Arc,
while Open/Close use the existing selector-aware FLT copy and construct a fresh
Arc. Its wrapper costs three work units and one record. The FLT leaf separately
accounts for its payload; guest text and ranged structural holes are copied
verbatim, without parsing or granting authority. Behavioral predicate names
remain inert under host-variable binding.

Optional native fields drop in place, unlike optional category fields. The
[flat-leaf model](../../formal/rocq/rho_bridge/theories/FlatBindingLeafReservation.v)
proves a two-work/one-record Option shell charge, plus the existing leaf charge
only when present. There is no replacement `None`, category dummy or child
cleanup task. The generated fixture uses production enum layouts and checks
required and optional mixed fields, `None` versus present-empty text, selector
opening/closing and failure after earlier native copies. This does not establish
full grammar-to-field-layout parity for every optional-capture syntax shape.

#### Scope fields and required vector fields

Scope and required-vector fields extend the same generated Visit/Assemble
worker and checked result slots; they do not introduce another clone engine.
The field descriptor supplies each child's actual category, including a scope
body whose category differs from its enclosing constructor. Assembly borrows
the original variant for native fields and scope patterns; the immutable root
borrow keeps those source pointers valid through normal-error cleanup.

Only Open and Close cross a scope body at the parent's depth plus one. The
worker admits that step before checking depth overflow, then schedules the
body with the incremented state and the unchanged external binder roster.
Scalar prefields keep the parent's state. Clone copies the scope pattern but
shares its body Arc, just as it shares scalar category Arcs. Pattern copying
uses the existing checked Binder or binder-vector leaf: it preserves identity,
diagnostic names, order and duplicates without freshening.

The [scope-field model](../../formal/rocq/rho_bridge/theories/ScopeBindingReservation.v)
adds seven work units and three records for a single-binder scope, or six work
units and three records for a multi-binder scope, to the existing required-body
Arc allowance and its selected dummy charge. These additions cover the scope
shells, extraction/replacement dispatch and replacement pattern. The original
pattern's copy and cleanup are charged separately by the
[pattern-copy contract](../../formal/rocq/rho_bridge/theories/BinderPatternCopy.v).
Raw `Scope::from_parts_unsafe` reconstruction preserves the transformed body;
it does not invoke closing again.

A required `Vec<Category>` differs from an Arc field: every stored element is
copied into an owned output occurrence in Clone, Open and Close. The element's
own scalar Arc boundaries still retain their normal Clone sharing semantics.
This applies both to regular fields and to required vector prefields before
a scope, such as a URI-list prefield. The existing generated Drop arms use
`mem::take` to leave an empty vector, then push one owned cleanup task per
stored element; they do not create a selected category dummy for the vector.

For actual vector length $`n`$, the
[required-vector model](../../formal/rocq/rho_bridge/theories/RequiredVecBindingReservation.v)
assigns local construction and cleanup $`10 + 4n`$ work units,
$`4 + 2n`$ records and zero owned bytes. Child production and cleanup, result
slots, checked takes, traversal-task operations and the parent's base allowance
are separate. The borrowed reverse walk additionally costs $`3 + n`$ work
units and one record, admitted before walking. These named iterator contracts
count construction, terminal advance and teardown, plus successful advances;
they are logical accounting boundaries, not physical allocation or instruction
counts. The walk uses the existing reverse-iteration projection without a
staging vector. Source-order slots and reverse task pushes preserve element
order and repeated occurrences.

Direct category-vector constructors and category-vector literals, such as
`List::ListLit(Vec<Proc>)`, use the same single-field descriptor and the same
checked assembly. Both existing Drop paths have the identical empty-vector
replacement and owned-child push loop, so the required-vector model applies
without a second reconstruction algorithm. This adaptation is local to checked
generation; it does not change the shared variant classifier. Primitive byte
vectors remain native leaves, not vectors of language-category terms.

Assembly admits destination storage before requesting vector capacity. Native
and pattern copies enter paid locals before any child take. It then takes all
scalar and scope children into bare category locals and vector children into
the admitted destination vectors, still without category Arc wrappers. A
refusal cleans up the produced vector prefixes and other paid locals using
their existing child allowances. Only after every take succeeds are Arc
wrappers, raw scopes and the parent formed, with no fallible callback until
publication. No child credit is refunded or charged again during that transfer.

This contract covers required vector fields and direct/literal category
vectors, not optional vectors, hash-based collections or native zipper carriers. Their
checked integration and remaining scope shapes are separate obligations.
Neither these local models nor this shared-worker increment establish complete
generated Rholang support, production activation, panic recovery or physical
resident-memory bounds.

#### Other collection reconstruction contracts

The [ordered-reconstruction model](../../formal/rocq/rho_bridge/theories/OrderedBindingReconstruction.v)
supplies the corresponding map, set and PathMap width and partition laws for
its existing insertion operation. Retained entry count cannot exceed the
admitted input-entry count, including when transformed keys collide. This is
stored width, not bag multiplicity or hash-table capacity.

The ownership model associates inventories of occurrence tags with keys and
values separately. Insertion and reconstruction preserve the multiset of tags
across retained and discarded inventories. If the input occurrence tags are
distinct, those inventories are disjoint; equal semantic values do not imply
equal occurrence tags. Summing any nonnegative per-tag credit conserves the
original credit across both inventories. These laws require the concrete
worker's key/value moves to match the modeled insertion operation; they do
not establish hash cost or destructor timing.

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

#### Admitted reconstruction stages

`HashBag::try_rebuild_entries_with` adds fallible admission around the same
native reconstruction operations. It consumes already-transformed entry/count
pairs and borrows the original bag. `CloneEntries` selects repeated `insert_n`:
positive counts accumulate, zero-count inputs are discarded, and the total is
recomputed. `BindingEntries` selects the binding recipe above, including retained
zero-count keys and the original total. These policies are deliberately distinct
from each other and from the bag's derived `Clone` implementation.

| Stage | Facts available to admission | Native work that follows acceptance |
| --- | --- | --- |
| `Start` | Mode, input width, source total | Empty output construction, input iteration and local container cleanup |
| `Insert` | Incoming key/count and borrowed retained entries | Checked Clone total addition, then the selected native insertion |
| `FinalBindingSummary` | Borrowed retained entries | Binding-only cached-summary reconstruction |

The retained-entry view exposes keys, counts, stored width and map capacity, but
not the unfinished summary. `distinct_len()` measures stored keys in constant
time without hashing them; `len()` measures multiplicity and cannot substitute
for it. Neither stored width nor capacity bounds structural key Hash/Eq work.

The caller must admit its own inspection, native insertion and growth, key
hashing/equality, and summary work before accepting a stage. The producer must
already have paid for the input vector, each owned key and their normal cleanup,
including refusal at `Start`. No implicit key-operation allowance is supplied.
Refusal publishes no bag and leaves the borrowed source unchanged. Current,
pending, retained and collision-discarded keys retain independent ownership and
are disposed exactly once. Clone count overflow rejects before native insertion;
the accumulator invariant also bounds an occupied entry's count addition.

The [staged bag model](../../formal/rocq/rho_bridge/theories/RequiredHashBagBindingReservation.v)
proves occurrence partitions, count invariants and conditional native-trace
coverage. The [runtime tests](../src/hashbag.rs) exercise both policies, collision
order and diagnostic retention, every refusal boundary, zero counts, overflow,
and cleanup. This staged interface does not by itself establish a concrete
generated key-cost provider or activate bounded public Rholang preparation.

#### Native hash-leaf admission

[`CheckedFxHashLeaf`](../src/checked_hash.rs) supplies the first concrete native
hashing boundary for `i64`, `bool`, `u8`, `usize`, `String`, `OrdVar`,
`Binder<String>`, `Vec<Binder<String>>`, `FltNode`, `Arc<FltNode>` and the cached
native hash of `HashBag<T>`. It is sealed
to these audited implementations. It first reserves logical work for metadata
inspection and checked receipt arithmetic, then reserves the complete native
call. Only then does it invoke the original `Hash::hash`
against the caller's actual `FxHasher`. No proxy hasher, intermediate digest,
byte buffer or replacement hashing algorithm is introduced.

The [hash-leaf model](../../formal/rocq/rho_bridge/theories/AdmittedKeyHashExecution.v)
defines bounded source groups rather than machine instructions. Signed `i64`
costs three native work units; the other fixed leaves cost two. String work
accounts for each bulk chunk, mix and byte load, including repeated short-input
loads and an overlapping final suffix. The bound covers both dependency
feature profiles: one emits the native string terminator and one omits it.
This does not assert identical hashes across those profiles; the original
implementation still determines the result in each profile.

The [structural-leaf model](../../formal/rocq/rho_bridge/theories/AdmittedStructuralKeyHash.v)
composes those native costs with the pinned Moniker 0.5.0 identity hashes and
the actual FLT fields. Free and bound variables cost 14 and 19 native work
units respectively; pretty-name hints are not hashed. A binder costs eight,
and a vector of $`n`$ binders costs $`7+10n`$. Their single inspection unit
reads only fixed metadata or vector length, not the hints or vector elements.
The original native call still visits every binder.

An FLT hashes its selector, all five diagnostic/source strings, actual holes
and pieces, ranges, bounds and position. Declared bounds are hashed scalar
fields, never trusted work receipts. Inspection borrows string lengths without
scanning text and uses two explicit iterator loops. Each loop reserves one
unit **before** advancing, including its terminal advance; successful total
inspection is $`3+h+p`$ units for $`h`$ holes and $`p`$ pieces. Checked additions
accumulate native execution work without retaining a plan. Arc forwarding adds
two native units, without cloning the Arc or its contents. Cancellation at any
inspection boundary still precedes the single whole-value native hash call.

The cached bag adapter reserves one inspection unit and 19 native work units
for the original two `usize` fields and four `u64` summary lanes. It invokes
no element Hash, Eq or Clone operation. This constant-size operation does not
certify a bag's keys, authorize insertion or validate unsupported descendants.
Its [scheduling model](../../formal/rocq/rho_bridge/theories/AdmittedGeneratedHashScheduling.v)
also states the ordered-call and pending-task laws for generated admission.

The initial supported build uses pinned `rustc-hash` 2.1.3, the audited x86-64
64-bit-pointer compiler revision, and its trusted standard prebuilt core.
The [build check](../build.rs) rejects unknown compiler revisions, wrappers and
detected sysroot/rebuilt-core overrides for this checked boundary. It is not an
attestation of arbitrary build environments. Unsupported profiles return
`UnsupportedProfile`; ordinary hashing remains available. Tests reporting native
correspondence must show that the profile-gated positive test actually ran.

Refusal or arithmetic overflow leaves the hasher unchanged. Earlier inspection
charges remain spent. A successful call returns its native execution allowance,
not an authority token: retaining it or paying for another execution is a
separate caller obligation tied to unchanged input and the same profile.
Borrowed byte reads consume work, not owned-byte retention. Hasher construction,
`finish`, generated worklists, other native leaves, equality and map operations
remain separate contracts; this leaf interface alone does not activate public
preparation or complete the generated HashBag admission provider.

`CheckedFxHasher` names the actual pinned hasher without introducing a proxy.
`CheckedIterativeHash` is the generated-worklist interface; declaring it alone
does not activate that worklist or public preparation. Its composite failure
contract differs from the single-leaf guarantee: a rejected later operation
may follow earlier hash writes, so the caller must discard the partial hasher.
Unsupported constructors carry their exact category and constructor names;
they do not invoke an unchecked fallback.

#### Admitted generated Hash scheduling

The [shared emitter](../../macros/src/gen/term_ops/iterative_hash.rs) now has an
internal checked mode alongside ordinary generation. It uses the same
constructor classifier, eager field prefix, reverse-pushed deferred suffix,
scope pattern/body order and category discriminants. Ordinary emission keeps
its generic hasher and thread-local worklist unchanged; complete captured
outputs are compared byte-for-byte as a regression gate. The checked mode is
not yet activated as the public Rholang preparation provider.

Checked tasks use a local vector because their fallible native callbacks carry
the caller's error type. An opaque task stores only a borrowed pointer and a
typed callback. Creating it performs no hashing: when that task is popped,
the callback invokes the existing audited native leaf operation against the
original hasher. No second hashing algorithm, intermediate digest or recorded
byte stream is introduced.

The [scheduling proof](../../formal/rocq/rho_bridge/theories/AdmittedGeneratedHashScheduling.v)
shows that successful admission preserves the original ordered calls and that
failure exposes only an already-executed prefix. Vector elements retain source
order after reverse scheduling; their length prefix executes first. Generated
optional fields retain their explicit `u8` tags, distinct from native derived
option hashing inside an FLT. Scope patterns execute before their bodies and
after pre-scope fields.

The resource convention remains logical source work and retained records,
not physical allocator capacity or wall-clock execution time:

| Boundary | Admission before the action |
|---|---|
| Local task-vector header and normal release | Two work units and one logical record |
| Task construction/push and possible pending disposal | Two work units and one logical record |
| Pop, including the terminal empty pop | One work unit |
| Category routing | One work unit |
| Vector metadata/iterator setup | One work unit |
| Each vector advance, including the terminal advance | One work unit |
| Native leaf execution | Its existing inspection and native-work contract |

Each logical record projects to four reservation units. Task payloads borrow
the root, so pending cleanup releases task storage without recursively dropping
AST children. The normal vector push may request allocation or growth; allocator
internals and relocation costs are outside this established logical convention.

The implemented internal profile covers audited scalar and structural leaves,
category children, optional fields, ordered category vectors, binder scopes,
and cached bag summaries. Map/Set/PathMap sorting, primitive byte vectors and
predicate-native branches currently return named constructor refusals before
their unadmitted operations. Required Map/equality and insertion coverage remain
necessary for public preparation. A cached bag hash does not inspect its members,
so this hash operation alone cannot establish whole-source profile admission.

The [generated fixture](../../macros/src/gen/term_ops/iterative_hash_checked_tests.rs)
uses production enum layouts and the existing Clone, comparison, Hash and Drop
emitters. It checks seeded native-digest equality, every reservation cutpoint,
exact/under work and record limits, explicit unsupported constructors, and
20,000 nested vector/scope levels on a 256 KiB native stack. These are focused
Rust correspondence tests, not a proof of all generated languages or public
node readiness.

#### Native comparison-leaf admission

[`CheckedNativeEqualityLeaf` and `CheckedNativeOrderingLeaf`](../src/checked_cmp.rs)
admit the existing native comparisons for `i64`, `bool`, `String`, `OrdVar`,
`FltNode` and `Arc<FltNode>`,
plus equality and inequality for `Binder<String>` and `Vec<Binder<String>>`. Equality
and ordering are separate sealed capabilities: an equality-only binder must not
acquire an ordering implementation merely to participate in checked equality.
The equality interface exposes both `eq` and `ne`; generated inequality checks
must retain their original `ne` operation rather than substitute an ordering
test. The ordering interface invokes the original `Ord::cmp`.

The [native comparison model](../../formal/rocq/rho_bridge/theories/AdmittedNativeLeafComparison.v)
uses one paid metadata group followed by a separate reservation for native
execution. Metadata inspection reads lengths and performs checked arithmetic;
it neither scans text nor compares payloads. With lengths $`l`$ and $`r`$, let
$`m=l`$ when the lengths are equal and $`m=0`$ otherwise.

| Operand type | Equality work | Inequality work | Ordering work |
|---|---|---|---|
| `i64` or `bool` | $`2`$ | $`2`$ | $`2`$ |
| `String` | $`6+2m`$ | $`7+2m`$ | $`9+2\min(l,r)`$ |
| `OrdVar`, both free | $`14`$ | $`15`$ | $`68`$ |
| `OrdVar`, both bound | $`19`$ | $`20`$ | $`14`$ |
| `OrdVar`, different variants | $`7`$ | $`8`$ | $`5`$ |
| `Binder<String>` | $`8`$ | $`9`$ | Not defined |
| `Vec<Binder<String>>` | $`7+11m`$ | $`8+11m`$ | Not defined |

These are logical source-group allowances, excluding the metadata unit.
`String` derives its comparisons over its `Vec<u8>` field, which reaches the
standard library's byte-slice comparison. The byte contribution covers both
operand ranges supplied to `compare_bytes`, including bytes after an early
mismatch. It is **not** a bound on physical machine loads, CPU instructions or
the internal implementation of `memcmp`. No byte buffer, replacement comparator
or owned payload is allocated by the adapter.

The build check uses the same audited compiler/target and trusted prebuilt-core
boundary as native hashing, but comparison does not depend on Fx hash semantics.
An unsupported profile refuses before metadata admission. Cancellation or
arithmetic overflow occurs before the native call, with previous inspection
charges still spent and both operands unchanged. Success returns the original
native result, not a reusable execution receipt.

The [identity-comparison model](../../formal/rocq/rho_bridge/theories/AdmittedIdentityComparison.v)
covers the original identity judgments. Diagnostic names do not participate in
these equalities. Bound-variable ordering evaluates both field comparisons;
free-variable ordering uses two fresh `DefaultHasher` instances over the unique
identities. Its source allowance is distinct from Fx hashing and does not
assume that hash equality implies identity equality. Vector equality admits the
full possible visited prefix, even when the native predicate stops early.

Generated scopes order their binder patterns using existing hash expressions,
not a `Binder::cmp` implementation. Two typed, documentation-hidden helpers admit
those expressions: `precharge_generated_single_pattern_order` reserves $`71`$
execution groups, while `precharge_generated_multi_pattern_order` reserves
$`5`$ for unequal lengths or $`27+80l`$ for equal lengths. Each first pays the
same metadata unit. Equal-width multiplication and addition are checked;
unequal lengths never visit or multiply the unused binder range. The generated
checked caller must then immediately evaluate its unchanged expression once.
The helper does not return a comparator or reusable authority. Scope-body
access and task scheduling remain separate charges.

Collection scheduling and the native HashBag insertion provider still require
their own composed contracts. The leaf interfaces and
pattern admission helpers alone do not activate bounded public preparation.

##### Structural FLT comparisons

The [FLT comparison inspector](../src/checked_cmp_flt.rs) preserves the whole
original native operation after paid metadata inspection. The
[FLT comparison model](../../formal/rocq/rho_bridge/theories/AdmittedFltComparison.v)
reuses the existing paid flat fold and native-execution composition. No guest
parser, template validator, hash operation or replacement comparator runs in
the inspector. All ten native fields remain part of comparison, including
diagnostic text, ranges, declared bounds and position.

Let $`E(x,y)`$ and $`C(x,y)`$ denote the logical equality and ordering allowances
for corresponding native components. For a node pair, let $`P_E`$ and $`P_C`$
be the sum of selector work and the work of the five top-level strings. The
strings use the byte-length rules above; the selector uses the identity rules.
For either operation, nested component work is:

| Paired component | Native execution allowance |
|---|---|
| Optional category strings, both present | $`6`$ plus String work |
| Optional category strings, any other case | $`5`$ |
| Hole declarations | $`16`$ plus name String work and optional category work |
| Two text pieces | $`14`$ plus text String work |
| Two hole pieces | $`18`$ |
| Different piece variants | $`5`$ |

For equal-length vectors, $`V_E=7+\sum_i(3+E_i)`$; otherwise $`V_E=7`$.
Ordering uses the common prefix: $`V_C=11+\sum_i(4+C_i)`$.
The node allowances are therefore $`E_N=29+P_E+V_E(holes)+V_E(pieces)`$,
$`N_N=E_N+1`$ and $`C_N=29+P_C+V_C(holes)+V_C(pieces)`$.
The sums reserve the whole possible native visited prefix, even when comparison
returns earlier. They do not assume equality is equivalent to an `Equal`
ordering result.

After one root metadata reservation, each selected vector pass reserves one
unit before every paired iterator advance, including its terminal advance.
Equality and inequality skip the pass for unequal-length vectors; ordering
always inspects the common prefix. The inspector uses actual vector and String
lengths, never declared template bounds as a size certificate. Checked sums
fail before native execution without refunding previous metadata work. The
implementation borrows the flat vectors without creating a paired roster.

| Arc relationship | Equality work | Inequality work | Ordering work |
|---|---|---|---|
| Same allocation | $`3`$ | $`3`$ | $`2+C_N`$ |
| Different allocations | $`4+E_N`$ | $`5+E_N`$ | $`2+C_N`$ |

Shared-Arc equality and inequality need only the root metadata group. Arc
ordering still inspects and compares the payload, even for the same allocation.
No Arc is cloned by admission. This preserves the standard library's separate
native paths; pointer identity is not generalized into a comparison shortcut.
The focused tests cover field-by-field parity, every small-fixture refusal
boundary, exact/under limits and sampled 20,000-entry flat-width checks on a
256 KiB stack. That is not a claim about arbitrary nested AST depth or complete
public preparation.

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
| String or byte vector | Reserve one record, actual bytes, copy work and flat cleanup before copying |
| Direct `FreeVar<String>` | Reserve its record, optional name bytes and cleanup of a present name; Moniker binding is a no-op on this type |
| Closing `OrdVar(Var::Free(...))` | Admit inspection and each ordered identity comparison; select the first matching identity, validate its `u32` index, then reserve the copy using the source name |
| Opening a matching-depth bound variable | Admit inspection; validate the roster index; reserve and copy the selected binder's identity and name |
| Other variable cases | Admit inspection and copy the unchanged variable |

A copy record costs one logical work unit and four logical retention units;
each owned byte adds one to each charge. Inspection and each identity comparison
cost one work unit without retained units. Owned String/byte-vector cleanup
adds one work unit, including for an empty owned buffer. A variable with a
present name adds one cleanup unit; `None` has no owned name to clean up.
Opening charges the selected binder's optional name, not the old bound hint.
Copy-only scalar and canonical numeric handles have no additional owned-field
cleanup. Arithmetic is checked before the
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

`Binder<String>` and `Vec<Binder<String>>` have explicit checked-copy
implementations for generated scope patterns. Moniker opens and closes these
patterns without changing them. Copies therefore preserve every identity and
optional name, including repeated identities and equal names with different
identities; they do not freshen or derive a replacement roster.

A Binder adds two logical work units for its wrapper construction and flat
cleanup. Its contained FreeVar supplies the storage record. A binder vector
first admits its header construction/cleanup and one record per entry, then
requests capacity for the entry count. Its iterative loop admits
entry insertion/cleanup dispatch, Binder wrapper work, and name-copy work and
bytes before each push. A private preadmission path reuses the same FreeVar
copy primitive without charging its already-reserved record twice; ordinary
FreeVar copying keeps its existing callback and charges.

For a vector with entry count $`n`$, present-name count $`p`$, and total owned
name bytes $`b`$, the work allowance is $`2 + 5n + p + b`$ and retention is
$`4(1+n) + b`$. These use the existing logical units, not allocator capacities.
The [pattern-copy model](../../formal/rocq/rho_bridge/theories/BinderPatternCopy.v)
proves exact pattern preservation, ordered-prefix laws and the record
prepayment identity. The [runtime tests](../tests/checked_binding.rs) compare
identities and names with Moniker, check every small-case cancellation point
and exact/under limits, and copy and partially clean up 20,000 binders on a
256 KiB stack. Scope-body traversal and generated-worker activation remain
separate obligations; these pattern helpers do not close a body again.

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

The [flat-leaf model](../../formal/rocq/rho_bridge/theories/FlatBindingLeafReservation.v)
assigns one normal teardown event to each FLT node, vector header, entry
dispatch and owned String field. For this specific flat shape, that tally
equals its measured payload-record count. Its base work is therefore twice
that count: copy work plus cleanup. Owned bytes are added once by the existing
reservation convention. This is not a generic rule for native records, and
the selector's copy/cleanup remains separately charged.

A standalone checked `Arc<T>` boundary reserves three work units and one
record for wrapper creation/copy, automatic release, and the last-owner check.
Open/close reuses the produced child's already-paid cleanup; shallow clone
keeps the source owner alive through normal-error cleanup. Generated category
fields have a different extraction/replacement lifecycle and must not reuse
this standalone-wrapper charge in place of their own field receipts.

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
