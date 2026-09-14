# Native HashBag resource admission

This design connects the existing `HashBag` reconstruction stages to the
[Rholang frontend admission contract](rholang-frontend-admission-contract.md).
Parallel-process bodies use `HashBag<Proc>`; opening a scope or replacing a
structural foreign-language term can reconstruct that bag. Paying for the
resulting worklist entries alone does not pay for the backing table, key
operations, or cleanup.

The reconstruction interface already exists in
[`runtime/src/hashbag.rs`](../../runtime/src/hashbag.rs). Concrete table and
key-operation coverage is still an implementation obligation. This document
records the audited source boundary and required refinement, not a claim that
checked parallel-process preparation or the public application is complete.

## Reuse and semantic identity

Use `try_rebuild_entries_with` and its `Start`, `Insert`, and
`FinalBindingSummary` stages. Each stage must be admitted before its original
native action, through the same preparation budget. Admission must also pay for
its own inspection and scratch storage.

| Existing policy | Meaning that admission must preserve |
|---|---|
| `BindingEntries` | Original visitation order; first equal key object, last supplied count; original stored total, including totals different from the surviving count sum; zero-count entries remain stored |
| `CloneEntries` | Existing generated reconstruction through `insert_n`; positive counts accumulate and zero-count incoming keys are discarded |
| Derived `Clone` | Native backing-map clone, distinct from `CloneEntries` reconstruction |
| Native `Hash` | Existing cached scalar summary stream; not a bound for descendant reconstruction |
| Native `Eq` | Stored-total equality followed by counts-map equality; neither equal hashes nor ordering equality is a substitute |
| Native `Ord` | Existing total-count and sorted-element ordering; not the definition of native equality |

The [existing reconstruction model](../../formal/rocq/rho_bridge/theories/RequiredHashBagBindingReservation.v)
already supplies ordered reconstruction, count, occurrence-ownership, partial
cleanup, and conditional native-trace coverage laws. Its `native_trace_cover`
premise must be instantiated from actual source behavior. It does not assign
constant costs to structural `Hash` or `Eq` calls.

The key operation reached during `HashBag<Proc>` reconstruction is generated
`Proc::eq`, not native `HashBag::eq`. Its `PPar` branch currently uses the
existing canonical collection comparison machine. Extend that checked machine
at its existing typed callbacks; do not introduce a counts-map equality
algorithm unless a required caller actually invokes one.

Zero-count entries require particular care: ordinary generated Bag comparison
constructs repeated roster items, whose constructor requires positive counts.
The checked roster rejects zero with `InvalidCollectionInput` before that
constructor. Admission must preserve this explicit boundary rather than
silently drop stored entries or claim that native Bag equality and ordering
are interchangeable. This does not change the binding reconstruction policy,
which can store zero counts and transport a differing original total.

## Exact library boundary

`HashBag` stores `std::collections::HashMap`, not the workspace's direct
hashbrown dependency. The source audit follows
[`runtime/build.rs`](../../runtime/build.rs): the trusted x86-64, 64-bit profile
uses compiler commit `2e2b193f8ada105f27608b7be81c293e0d7292cb`. Its standard
library selects hashbrown 0.17.1. Arbitrary compiler wrappers, rebuilt standard
libraries, and replacement sysroots are not certified by that profile.

The source files are under the directory reported by `rustc --print sysroot`,
relative to `lib/rustlib/src/rust/library/`:

| Source | SHA-256 of the audited file |
|---|---|
| `std/Cargo.toml` | `caa5a4748d5372fb9bcb32277830488fcbcb1dfa35db5ac6f6d1d8408e849f75` |
| `std/src/collections/hash/map.rs` | `8db811482220b0d8586619bd4f11bfea00939fa056ed0a1e7b383911efb73d03` |
| `vendor/hashbrown-0.17.1/src/raw.rs` | `0c8ad353ba95817e72b0a8fea48fa2599099ea3def374f254ab6402a9c468d22` |
| `vendor/hashbrown-0.17.1/src/map.rs` | `b79497ce537ffc5ed4f8f3399434b9216c01e7927fdc434fee190e9e9ce2abb0` |
| `vendor/hashbrown-0.17.1/src/rustc_entry.rs` | `35212ecf4d0195954aa6ecc6c0b8e99a8628dffb4fb101fa67d3d7a31a52b837` |
| `alloc/src/alloc.rs` | `41c7f678fb68d3a52d20399e96903716567b318dd9bbfc0da4e66a1b06f9b4d4` |

Standard `HashMap` uses `Global` by default. In this pinned implementation,
`Global::alloc_impl_runtime` returns a slice with the requested logical length
(`alloc.rs`, lines 303–314). Consequently, hashbrown's oversized-allocation
adjustment (`raw.rs`, around line 1580) does not enlarge this table's bucket
count. This is not an assertion about physical allocator overhead or arbitrary
allocator implementations.

## Why current capacity is insufficient

Define the following scalar properties of one native table:

| Symbol | Meaning |
|---|---|
| $`B`$ | Bucket count; the unallocated singleton has one sentinel bucket |
| $`I`$ | Number of occupied buckets, independently of bag multiplicities |
| $`D`$ | Number of deleted control entries, often called tombstones |
| $`G`$ | Native `growth_left` counter |
| $`C(B)`$ | Full effective capacity of this bucket allocation |
| $`H`$ | Historical maximum observed `counts.capacity()` at completed mutation boundaries |

The pinned formulas are:

```math
C(B)=\begin{cases}
B-1 & B\leq 8,\\
7\lfloor B/8\rfloor & B>8,
\end{cases}
\qquad \mathrm{capacity}=I+G.
```

Deleting an occupied bucket can change its control entry to `DELETED`, decrement
`items`, and leave `growth_left` unchanged. Thus public capacity decreases while
the allocation remains unchanged. Neither current capacity nor current entry
count recovers that allocation's scan extent. An empty allocated table must
not be confused with the unallocated singleton.

The metadata design preserves the stronger boundary invariants:

```math
C(B)=I+D+G,\qquad C(B)\leq H.
```

Valid allocated sizes are powers of two starting at four. Their exact capacity
formula gives the following bound; the singleton is handled separately:

```math
B\leq 2C(B)\leq 2H,
\qquad B\leq\max(1,2H)\text{ including the singleton}.
```

These inequalities must be derived from the source-shaped transition model,
not supplied as assumptions about a finished Rust operation. Computing a
machine-word allowance from them must use checked arithmetic and reject before
the scan on overflow. A mathematical natural-number bound is not itself a
checked machine-word implementation.

The [extent model](../../formal/rocq/rho_bridge/theories/NativeHashBagExtent.v)
establishes the capacity arithmetic, initialization, and raw counter-transition
laws. The [history model](../../formal/rocq/rho_bridge/theories/NativeHashBagHistory.v)
derives the boundary invariant and bucket bound by induction over completed
insertions, erases, clones, and fresh-table resets. Neither model assumes the
history bound as a transition premise. Resize sizes are overapproximated by
valid native bucket sizes with sufficient room; the proof does not yet verify
allocation rounding, scan coverage, or prepayment.

The Rust owner maintains `capacity_high_water` at these operation boundaries
and exposes it through the constant-time `historical_capacity()` query. The
[focused regression tests](../../runtime/src/hashbag_history_tests.rs) compare
that field against independently observed native capacities, including real
tombstones, replacement-triggered growth without a new key, inherited clone
history, and all binding-table reset paths. They also check that differing
allocation histories leave native equality, ordering, and hash bytes unchanged.
This validates metadata maintenance on the tested profile, not the unfinished
concrete traversal allowance or end-to-end frontend admission.

## Mutation and observation order

Reserve/rehash/resize and the final lookup result are distinct steps. In
particular, `HashMap::insert` calls `find_or_find_insert_index`, whose
`reserve(1)` precedes searching (`raw.rs`, lines 1120–1143; `map.rs`, around
line 1806). Replacing an existing binding key can therefore resize the table
without increasing its entry count. By contrast, standard `HashMap::entry`
delegates to `rustc_entry` (`std/src/collections/hash/map.rs`, around line 1012),
which searches first and reserves only for a vacant result (`rustc_entry.rs`,
lines 35–49). This is the path used by bag `insert` and `insert_n`, not
hashbrown's separate public `entry` method.

The equality operand order also differs: binding insertion calls the incoming
key's equality on a retained candidate; the standard entry path calls the
retained candidate's equality on the incoming key. Preserve those exact
operands when covering structural work. Equality of results does not establish
equal execution costs in the two directions.

| Native effect | Scalar update before the metadata observation |
|---|---|
| Found existing key, without reserve-side changes | Counters unchanged |
| Insert into an empty bucket | Increment $`I`$ and decrement $`G`$ |
| Insert into a deleted bucket | Increment $`I`$ and decrement $`D`$ |
| Completed rehash in place | Preserve $`B,I`$; set $`D=0`$ and $`G=C(B)-I`$ |
| Completed resize | Select the new native allocation; preserve $`I`$; set $`D=0`$ and $`G=C(B)-I`$ |
| Erase to empty | Decrement $`I`$ and increment $`G`$ |
| Erase to deleted | Decrement $`I`$ and increment $`D`$ |
| Fresh backing-map replacement | Restore the singleton and zero history |
| Successful native clone under `Global` | Preserve the source bucket/control state and inherited history |

After a completed insertion, observe the resulting public capacity and retain
the maximum of it and the previous history. Deletion retains history. After
resize or rehash there are no tombstones; a subsequent insertion into an empty
bucket preserves full observed capacity, and finding an existing key preserves
it too. This is why observing at the completed wrapper boundary can establish
the invariant even when an internal allocation changed first.

Audit every owner mutation: `insert_binding_entry`, `insert`, `insert_n`,
`remove`, the close/open binding rebuilds, `visit_mut_vars`, fresh construction,
and derived cloning. A clone must inherit history rather than recomputing it
from a potentially sparse source's current capacity. Metadata does not affect
Hash, equality, ordering, counts, retained key objects, or visitation order.

This boundary concerns completed operations and normal returned errors. It
does not prove invariance after an arbitrary interrupted native mutation or
panic unwinding. Nor can a capacity observation made after growth be used as
prepayment for that same growth.

## Borrowed iteration accounting

The borrowed-roster path must use the original iterator through explicit
`next` calls. Native specialized `fold` paths and consuming cleanup require
their own source correspondence; they are not silently covered by this one.
`RawIterRange::new` loads one aligned group even for an empty bag. Each
successful mask probe extracts and clears the lowest occupied position.
Exhausting a mask advances to the next group. The outer `RawIter::next`
checks the remaining entry count before probing a mask, so the terminal call
does not scan an empty suffix (`raw.rs`, around line 3851;
`control/bitmask.rs`, around line 102).

Let $`n`$ be the number of stored entries and $`L`$ the number of groups
actually loaded by a complete pass ending at its first `None`. The
source-shaped scan refinement tracks the following events separately:

| Native event | Complete-pass count |
|---|---|
| Aligned control-group loads, including construction | $`L`$ |
| Successful mask probes and lowest-bit clears | $`n`$ each |
| Exhausted mask probes and group advances | $`L-1`$ each |
| Outer `next` calls, including the terminal call | $`n+1`$ |
| Key/count pair projections | $`n`$ |

For this profile, a control group spans sixteen bytes. One group-load event
and its byte span are distinct quantities. With historical bucket allowance
$`E`$ and group allowance $`Q`$:

```math
E=\max(1,2H),\qquad
Q=1+\lfloor(E-1)/16\rfloor,\qquad
1\leq L\leq Q.
```

The [finite scan model](../../formal/rocq/rho_bridge/theories/NativeHashBagBorrowedScan.v)
establishes local remaining-count and original-slot-order preservation, and
derives that searching an empty mask with entries remaining has another group
available. It also derives event-count conservation for every actual prefix.
The [scan-bound composition](../../formal/rocq/rho_bridge/theories/NativeHashBagScanBound.v)
uses those laws and the history invariant to cover every prefix componentwise,
and then under declared nonnegative event weights. The concrete implementation must check arithmetic and
reserve the scan before constructing the iterator. Existing checked-roster
allocation and push charges remain separate; neither a stored-entry count nor
the iterator's exact output length alone pays for sparse control-group scans.

At one logical scalar-work unit per event plus sixteen read-work units per
control-group load, the native borrowed-pass allowance is $`4n+19Q`$, with no
owned payload units. Fixed iterator/adaptor setup is grouped in `Construct`;
native bucket and key/count projections are grouped in `Yield`. Metadata
inspection and the caller's loop remain separately charged. Borrowed iterator
destruction invokes no key destructor.

The adapter also relies on the native invariant that `counts.len()` and raw
`items` equal the number of `FULL` control entries. The model's arbitrary
Boolean control predicate is explicitly tied to that same immutable table in
the final adapter theorem. Scalar history reachability alone does not assert
this equality for an arbitrary predicate. Bag occurrence multiplicity and its
transported total are not substitutes for this native stored-entry count.

`HashBag::try_comparison_roster` implements this borrowed path using the
existing `CheckedCmpRoster`. It checks the audited profile and pays for
metadata inspection, computes the allowance with checked arithmetic, reserves
flat roster storage, and pays the native scan allowance before constructing
the iterator. Each explicit consumer advance and repeated-item push retains
its existing cancellation point. The source keys and stored counts are passed
through unchanged, and a partial refusal drops only the paid flat roster.

The [roster regressions](../../runtime/src/hashbag_roster_tests.rs) cover real
sparse/tombstone history, original pointers and entry order, absence of key
operations, every reservation cut, exact and one-under limits, stored-zero and
count-sum overflow refusals, and transported-total distinctions. This adapter
does not itself pay for sorting or key comparisons, or admit consuming
reconstruction. Generated comparison adds the existing owned comparison
machine and its typed child callbacks as described below.

## Generated comparison initialization

The [initialization model](../../formal/rocq/rho_bridge/theories/GeneratedBagComparisonInitialization.v)
connects the repeated-item adapter to the existing paid-roster model. A
successful walk preserves each original borrowed key, absent secondary value,
positive count, and native iteration position. Its cached total equals the
sum of those counts and fits the checked maximum. The general append lemma
requires the initial cached total to fit too; an empty source does not validate
an arbitrary pre-existing total. Fresh generated rosters start at zero.

Both public comparison constructors call the same private
`CollectionCmpPda::from_parts` initializer with five value arguments: lead,
left entries, right entries, left repetition sum, and right repetition sum.
Checked admission adds reservation and refusal behavior, not a different
sorting machine. Initialization correspondence concerns those exact arguments;
it does not assume the final comparison result or introduce another comparator.

The generated Bag factory computes the stored-total ordering first, then
builds both original rosters, then initializes that shared machine. An unequal
lead must not skip either roster: ordinary construction also builds its
arguments before the machine can return that ordering. Consequently, a stored
zero count or overflowing repetition sum produces the named checked refusal
even when the two stored totals differ. Root-alias equality may retain its
existing shortcut; malformed-input tests must not confuse that shortcut with
an executed collection factory.

Ordinary `map`/`collect` may use the native specialized `fold`, whereas the
checked adapter uses explicit `next`. Both visit increasing control groups and
the lowest remaining occupied position within each group, giving the same
ordered values. Their terminal mask-probe counts differ. This value-order
correspondence does not extend the borrowed `next` cost proof to `fold`.

The constructor census keeps operational support separate from eligibility
for its existing formal row vocabulary. That vocabulary has paired maps but
no weighted Bag field. A whole Bag-bearing row therefore has an explicit
unprojected `U` record, together with its full operational carrier checks and
both original generated arms. It must not receive an invented formal field or
a false runtime-refusal annotation. This initialization proof does not establish
the outstanding whole-category factorization for nested weighted collections.

The [generated comparison regressions](../../macros/src/gen/term_ops/iterative_cmp_checked_tests.rs)
exercise the existing production-layout fixture rather than a second language
or comparison implementation. They check ordinary/checked equality and order,
insertion permutations, repeated counts including the maximum machine-word
count, sparse history, transported-total anomalies, nested bags and maps,
scope bodies, every small reservation cut, exact and one-under budgets, and
20,000-level Bag traversal with teardown on a 256 KiB stack. Malformed counts
use named-error checks without invoking the potentially panicking ordinary
oracle. The [actual Rholang constructor census](../../macros/src/gen/term_ops/iterative_cmp_census_tests.rs)
also checks the `PPar` and `BagLit` factories and original typed callbacks.
These checks do not establish complete Rholang scope-opening/reconstruction
or public-node behavior; those source contexts remain separate acceptance
obligations.

## Remaining concrete coverage

The extent invariant is one input to admission, not the complete allowance.
The next refinements must establish:

1. Control-group scanning for the remaining consumers, especially consuming
   cleanup. The borrowed next-based path above has its own coverage; it must
   not be reused as a proof of specialized folding or owned iterator teardown
   without checking those actual source paths and ownership effects.
2. Lookup probing and actual key comparisons. The triangular group probe is
   separate from the sequential iteration walk. Bound its real probe and
   callback behavior, not just the number of returned entries.
3. Growth before action. The reconstruction accumulator starts empty and only
   inserts, so proving that it has no tombstones excludes the in-place
   compaction branch. The remaining resize loop hashes each retained record
   once, but its new-table probes and storage also need admission.
4. Required generated key `Hash` and native `Eq`, including nested parallel
   processes; retained-key rehash; both binding-summary hash passes; and the
   provider's own inspection. Cached bag hashes do not establish these costs.
5. Composition with the existing stack-safe source worklist, output receipts,
   and normal cleanup, preserving one shared budget and all original entries.

Acceptance requires actual required Rholang source contexts, not just the
generic collection fixture. Sparse/tombstone sources, collisions, aliases,
duplicate and zero counts, transported-total anomalies, overflow, each refusal
boundary, native parity, and small-stack teardown remain part of that check.
The allowance is a declared logical-work/storage contract, not measured RSS,
semantic funding, or a claim of arbitrary allocator behavior.
