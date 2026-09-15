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

## Inspecting native leaf work without replay

The existing sealed [hash leaf interface](../../runtime/src/checked_hash.rs)
exposes `try_inspect_hash_fx_work`. It performs the same paid metadata
inspection as `try_hash_fx`, but neither reserves execution nor invokes
`Hash`. The existing [comparison leaf interfaces](../../runtime/src/checked_cmp.rs)
likewise expose `try_inspect_native_eq_work`, `try_inspect_native_ne_work`,
and `try_inspect_native_cmp_work`. Equality, inequality and ordering retain
their separate native operations; equality-only binders acquire no ordering.

Each result is a source-specific logical-work allowance, excluding inspection
charges already spent. It is not execution permission. A caller must separately
reserve the original operation's work on the same unchanged borrowed operands
and audited profile, and pay for any retained accounting storage. Hasher
creation and finishing remain separate caller operations. Unsupported profiles
refuse before inspection; arithmetic overflow and reservation failure preserve
their original error kinds and do not refund earlier metadata work.

The ordinary checked-execution methods use the same private inspector, followed
by their original execution reservation and native call. The extraction reuses
the inspection/execution separation in the
[hash model](../../formal/rocq/rho_bridge/theories/AdmittedKeyHashExecution.v),
[structural hash model](../../formal/rocq/rho_bridge/theories/AdmittedStructuralKeyHash.v),
and [comparison model](../../formal/rocq/rho_bridge/theories/AdmittedNativeLeafComparison.v).
Inspection does not hash into a scratch hasher or execute an extra comparator.
The tests compare metadata-only reservation prefixes with the existing full
execution schedules, including structural FLT metadata and refused advances.

These are leaf interfaces, not complete generated-category allowances. A
cached Bag hash still covers only its summary, not descendant reconstruction.
The generated category traversal, nested collection comparison, and movement
of retained roots during resizing must supply their own coverage before these
allowances can be composed into a complete reconstruction provider.

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

## Prospective growth before insertion

The [growth refinement](../../formal/rocq/rho_bridge/theories/NativeHashBagGrowth.v)
derives the selected allocation from the pinned source's sizing function.
For a one-entry reservation, valid counters reduce the resize request to
$`C(B)+1`$. The source's small-capacity branch applies below fifteen; the
counts tuple contains a machine-word count, so its minimum capacity is three.
The singleton selects four buckets. Each allocated table selects twice its
previous bucket count, including the small eight-to-sixteen-bucket step.

Let $`B'`$ be the bucket count after optional reservation and insertion, and
$`I'`$ the resulting number of stored entries. The existing history invariant
and the derived allocation selection give the prospective bounds:

```math
B'\leq\max(4,4H),\qquad I'\leq I+1.
```

Here $`H`$ is the history **before** insertion. The model also proves that the
completed insertion preserves history reachability. Its optional-reservation
relation refines the earlier native transition projection; it does not assume
the desired bound as a resize premise. The unchanged branch deliberately
includes skipped reservation and does not identify which native lookup guard
was taken.

A reconstruction accumulator starts without tombstones, and insertion
preserves that property. When such a table has no growth credit, its stored
entry count equals full capacity. The native in-place compaction condition
cannot hold, so a required reservation selects resize instead. An update to a
found binding key can still take that resize, as explained above.

The [growth regression](../../runtime/src/hashbag_history_tests.rs) exercises
public capacities three through 112 using separate binding and entry-based
accumulators with colliding keys. It checks that binding reservation can grow
before finding an existing key, whereas an occupied entry update does not.
It does not inspect raw table addresses or certify allocation costs.

These results concern successful native arithmetic under the pinned `Global`
allocation contract. A concrete admission provider must still check machine
arithmetic and table-layout limits before the original insertion. Checking
the bucket bound alone does not establish those guards, account for retained
key rehashing, or pay for the new table's lookup and storage work.

## Exact allocation geometry

`HashBagRetainedEntries::checked_bucket_count` recovers the actual current
bucket count from a reconstruction accumulator's public capacity. The view's
private construction boundary guarantees a fresh, insert-only table observed between
completed native operations. The growth model proves that these tables have
no tombstones and that their public capacity equals full capacity. This is
not an inverse for arbitrary bags after deletion.

The inverse returns one for capacity zero (the unallocated singleton), four
for capacity three, and eight for capacity seven. For larger capacities it
requires divisibility by seven, multiplies the quotient by eight with checked
arithmetic, and requires a power-of-two result. The model proves exact recovery
and that native representable buckets satisfy those arithmetic guards.
The query checks the audited profile first and performs no allocation, key
hashing, or equality. Its caller must prepay the inspection. The singleton
must remain separate from allocated-table layout calculations below.

`HashBagRetainedEntries::checked_table_layout` computes the chosen table's
layout without allocating it. It reuses `Layout::array::<(T, usize)>` for the
entries and extends that layout with the native control-byte region. It does
not call `pad_to_align`: the native allocation's final size is unpadded.
The query rejects an unaudited profile, invalid allocated bucket count, or
unrepresentable layout. Its caller must check the profile and admit this
inspection before using it; the query is not itself resource admission.

Here $`B`$ denotes the actual chosen allocated bucket count, not the historical
extent allowance. Let $`s`$ be the tuple's byte size, $`a`$ its alignment,
$`A`$ the native control alignment, $`d`$ the data-region size, and $`\ell`$
the full requested allocation size. On the audited profile:

```math
A=\max(a,16),\qquad d=sB,\qquad \ell=d+B+16.
```

The [layout model](../../formal/rocq/rho_bridge/theories/NativeHashBagLayout.v)
proves that the tuple and bucket geometry make $`d`$ divisible by both $`A`$
and sixteen. Thus the standard extension and native rounding have exactly
the same offset, size, and alignment. Writing $`M`$ for `isize::MAX`, the
native size ceiling and the standard layout ceiling coincide:

```math
\ell+(A-1)\leq M.
```

Accepted native geometry also validates both intermediate standard layouts,
so composing those APIs adds no spurious layout rejection. The proof bounds
the native multiplication/addition intermediates and the local probe additions
when the source's position and stride guards hold. It does not prove that a
whole lookup reaches those guards, account for allocator work, or turn a
historical bucket upper bound into the actual selected allocation.

The [allocation-free layout regression](../../runtime/src/hashbag_history_tests.rs)
compares the query with the pinned native arithmetic across every machine-word
bucket power, including overflowing layouts, ordinary tuples and over-aligned
keys. Large boundary cases compute layout values only; they allocate no table.

## Lookup probe sequence

Native lookup and insertion use a triangular group probe, not the sequential
iterator walk. For an allocated table with $`B\geq16`$, define the number of
groups as $`q=B/16`$, the initial bucket position as $`p_0`$, and the triangular
numbers and subsequent probe positions as follows:

```math
T_0=0,\qquad T_{k+1}=T_k+k+1,\qquad
p_k=(p_0+16T_k)\bmod B.
```

The [probe-sequence algebra](../../formal/rocq/rho_bridge/theories/NativeHashBagProbeSequence.v)
derives that the first $`q`$ triangular residues modulo $`q`$ permute the whole
range from zero through $`q-1`$. It uses the fact that $`q`$ is a power of two
and proves injectivity through parity and divisibility; coverage is not an
assumption. It also proves the incremented-stride recurrence and the exact
formula retaining the initial offset modulo sixteen. These are shifted,
possibly unaligned windows, not the aligned groups of the iterator model.

The [control-window model](../../formal/rocq/rho_bridge/theories/NativeHashBagProbeWindows.v)
identifies each loaded lane with its original bucket or EMPTY padding. Large
windows read shifted circular originals; four- and eight-bucket windows read
an original suffix, padding, then a mirrored prefix. Each individual window
visits its original buckets without duplicates. With FULL and DELETED counts
associated with the same valid native controls, it also derives a positive
number of EMPTY originals.

The [full-cycle composition](../../formal/rocq/rho_bridge/theories/NativeHashBagProbeCoverage.v)
then derives that all original buckets occur exactly once across the first
$`q`$ shifted windows. It explicitly proves the integer-to-natural conversion,
translated group permutation, and flattening into the circular bucket range;
coverage is not an input assumption. An original EMPTY witness therefore
appears in a physical lane of that mathematical cycle, provided the actual
control bytes have the stated original/mirror/padding association. This
witness interface does not require completed native counters, so the resize
occupancy ledger can supply it too. Small tables obtain an EMPTY padding
lane in their first window; the static singleton is handled separately.

The [native mask refinement](../../formal/rocq/rho_bridge/theories/NativeHashBagProbeMasks.v)
connects each sixteen-bit mask to its exact ordered matching lanes and proves
the optional lowest-set-bit characterization. It retains the full seven-bit
tag range, including collisions: a matching tag is only an equality candidate.
The model proves that a matched lane identifies an original FULL bucket, not
padding, and that the native bitwise mask computes its original index. The
small mirrored windows and large circular windows are covered separately.
An EMPTY lane also guarantees that the combined lookup's insertion cache can
be filled before its EMPTY test, without assuming that the cache was already
populated. This does not assert that a cached small-table index needs no repair.

These results use the specified SSE2 mask and least-set-bit instruction
contracts; they do not verify compiler lowering. The
[mask-iteration refinement](../../formal/rocq/rho_bridge/theories/NativeHashBagMaskIteration.v)
proves that the native operation `word & (word - 1)` removes exactly the least
set bit. Subtraction occurs only after a successful lowest-bit result, which
proves the word is nonzero. Every successful-return prefix preserves the
original ordered suffix, repeats no lane, and returns at most sixteen lanes.
A consumer stopping at its first `None` has returned every original matching
lane exactly once. Repeated calls after `None` are not counted as successful
returns or bounded by this theorem. These are mask-iterator facts, not a bound
on arbitrary callback bodies or the number of groups reached by a lookup.

The [group-control refinement](../../formal/rocq/rho_bridge/theories/NativeHashBagProbeControl.v)
connects the mathematical cycle to the native continuation guards: lookup
requires no EMPTY lane, combined lookup first fills its absent insertion
cache and then tests EMPTY, and insertion-only search requires no special
lane. Its unbounded natural-number model has no step-limit or overflow
premise. It conservatively omits early successful equality returns, which
can only shorten a group-search prefix; it does not omit the cache update.

An original EMPTY witness supplies a barrier in the first $`q`$ windows.
The actual guard forbids advancing from that barrier, so every modeled
prefix visits at most $`q`$ groups and makes at most $`q-1`$ moves. The
position recurrence and derived stride bound then let the layout theorem
validate both ordinary machine additions before masking. Machine safety
is a consequence of the bound, not a premise used to establish it.
Four- and eight-bucket tables have EMPTY padding in their first group;
the singleton has static EMPTY controls. Their group search never advances.

The source interpretation must still associate those immutable controls,
initial position, and mode with the actual native call. The group theorem
does not prove termination or costs of equality callbacks, nor their
candidate-before-EMPTY evaluation order. That inner-body correspondence and
its mask-iteration accounting remain separate. Small-table insertion-index
repair can perform an additional aligned load, excluded from the group
bound. No modular-arithmetic identity is permission to assume wrapping
addition in the native implementation.

### Small-table insertion-index repair

The [insertion-repair model](../../formal/rocq/rho_bridge/theories/NativeHashBagInsertRepair.v)
retains the origin of the cached insertion index: it was selected by the
original special-lane mask from a window of the same immutable controls.
Filling an absent cache preserves that origin. A numeric index in range is
not sufficient by itself to justify the native repair operation.

For tables with at least sixteen buckets, the original/mirror association
makes that selected index non-FULL, so the repair branch is unreachable.
For four- and eight-bucket tables, an EMPTY padding lane can instead mask
onto an occupied original bucket. The native FULL test then triggers one
aligned control-group load at offset zero and returns its lowest special
lane directly, without another probe or index mask.

The repair's valid destination follows from an original non-FULL witness,
not merely from trailing EMPTY padding. The aligned scan selects a special
lane no later than that witness, hence before the end of the original table.
The model derives a valid non-FULL destination and either zero or one extra
aligned load. It does not count key callbacks, establish pointer provenance,
or certify the control allocation's initialization and alignment. The static
singleton is not an allocated insertion-repair target.

The [small-table regression](../../runtime/src/hashbag_history_tests.rs) uses
actual native allocations and an observed Fx hash to exercise both table
sizes. It checks that equality candidates beyond EMPTY padding are still
visited before the stop decision, that binding and entry lookup preserve
their original operand directions, and that repair produces the expected
native iteration order. These observable checks complement the source model;
they do not instrument control-group loads or prove arbitrary callback costs.

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

`HashBag::try_for_each_entry` exposes the same paid native scanner to binding
without allocating an intermediate pointer roster. It checks the profile,
pays metadata inspection, computes the history-based allowance, and then pays
the scan before iterator construction. Each consumer advance is separately
admitted. The visitor receives the same reservation callback, so its own
task, storage, or key-operation work can be paid before execution without
creating a new budget. Comparison retains its original allocation and
reservation ordering; repeated-item validation remains inside its visitor.

The [entry-projection refinement](../../formal/rocq/rho_bridge/theories/NativeHashBagEntryVisit.v)
maps the existing native scan's original slots to unchanged borrowed key/count
pairs. Every prefix preserves their order, and stopping visits every original
pair. There is no positivity or count-sum premise: binding must retain stored
zero counts and must not reinterpret its transported total. A yielded pair
counts a visitor attempt, including an attempt that returns an error, not
necessarily a successful visitor return. Earlier visitor effects are not
rolled back; any owned result already taken needs its existing cleanup credit.
The scanner itself performs no key operations and grants no visitor-work,
insertion, or reconstruction allowance.

Binding errors preserve unsupported profiles, unsupported constructors, and
invalid collection input separately from reservation and arithmetic failures.
Conversions from native Hash and comparison failures move an existing
admission error through unchanged. The [scan and visitor regressions](../../runtime/src/hashbag_roster_tests.rs)
check unchanged comparison reservation traces, original borrows in sparse
tables, zero counts and overflowing count sums, every scan/visitor refusal,
and zero, exact, and one-under work limits.

`HashBagRetainedEntries::try_for_each_entry` reuses that same scanner during
reconstruction, when the binding hash summary is not yet valid. Its private
construction boundary permits recovery of the exact current bucket count.
The entry-projection model derives the scan bound directly from that table's
group count; it does not invent a capacity history or substitute completed
counters for an in-progress resize table. With exact $`B`$, the group allowance
is $`Q=1+\lfloor(B-1)/16\rfloor`$, including the singleton's initial load.

The retained visitor pays metadata inspection before recovering geometry and
pays the full native scan before creating the iterator. Its typed inverse
distinguishes malformed capacity shapes from arithmetic overflow; the separate
public `checked_bucket_count` query keeps its original optional-result API.
Visitors still pay their own effects, and zero counts pass through unchanged.
The retained-entry regression checks original pointer/count order and every
reservation cut at real Clone and binding reconstruction stages, across
empty, growing, duplicate, and zero-count cases. Neither visitor constructs
a second roster or performs key hashing, equality, or cloning itself.

## Native resize correspondence

Resizing uses `FullBucketsIndices`, not the borrowed `RawIter` wrapper. The
[resize-scan projection](../../formal/rocq/rho_bridge/theories/NativeHashBagResizeScan.v)
maps its local control-mask bits and aligned group offset into the existing
scan cursor. It preserves the original occupied-slot order and remaining-item
guard: construction loads the first group, but exhaustion does not scan the
empty suffix. The source association must identify the same immutable old
controls, native item count, and local masks. Hashing, placement, copying, and
allocation release are not scan events.

The new table's intermediate controls cannot be interpreted through its
native `items` counter. That counter remains zero until relocation finishes;
`growth_left` likewise retains the initial full capacity. The
[occupancy model](../../formal/rocq/rho_bridge/theories/NativeHashBagResizeOccupancy.v)
instead associates actual FULL controls with a finite ledger of completed
source/destination pairs and at most one pending pair:

| Native point | FULL destinations | Initialized destination records |
|---|---|---|
| Before the next placement | Completed pairs | Completed pairs |
| After setting its tag | Completed pairs plus pending pair | Completed pairs |
| After copying its bytes | Newly completed pairs | Newly completed pairs |

The ledger preserves the original scan prefix and counts the pending tag
even before its bytes are initialized. Distinct, in-range destinations give
the exact number of FULL originals. The existing growth theorem supplies
capacity for every original record and an additional insertion, so a
non-FULL original remains available throughout relocation. Fresh target
controls contain only EMPTY or FULL, never DELETED; under that source
association, non-FULL means EMPTY. Lookup termination and the actual choice
of a destination remain obligations of the probe model.

Each old record is hashed once and placed into the new table without key
equality, cloning, or destruction. A byte copy does not transfer destructor
ownership at that point: the old table retains that authority throughout the
loop. Only successful final counter assignments and `mem::swap` transfer it.
The resize guard then frees the old allocation without rescanning or dropping
the relocated keys. These are allocator invocations, not constant-time or
physical-memory claims. Panic-path admission is separate from these normal
completion laws.

The same occupancy ledger bounds the flat relocation blocks. Let $`n`$ be
the original stored-entry count, $`c`$ the completed-copy count, $`p`$ the
pending-tag count (zero or one), $`u`$ the unread count, and $`s`$ the tuple
size in bytes. Its original-roster equation gives $`c+p+u=n`$. The transfer
allowance assigns each tagged record two control writes and two bucket-pointer projections, even
when the two control addresses coincide. Reserving $`s(c+p)`$ copy bytes
covers the pending record before its copy finishes and is bounded by $`sn`$.
At completion there are exactly $`n`$ copied records and $`sn`$ copied bytes.
These are transfer counts, not a claim that a Hash callback, placement probe,
or allocator body costs one unit. Control initialization, iteration, those
variable-cost bodies, and finalization remain separate from this allowance.

The [native resize regression](../../runtime/src/hashbag_history_tests.rs)
checks growth across small and larger tables using colliding keys. It records
the incoming hash, one rehash per old key in original scan order, subsequent
incoming-to-retained equality calls, and destruction of the duplicate incoming
key while retaining the first key object. The retained originals are neither
cloned nor dropped during resize and are each dropped exactly once at final
container destruction.

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

On the pinned profile, the original standard `HashMap` iterator implements
`ExactSizeIterator` but not `TrustedLen`. Ordinary `map`/`collect` therefore
takes `Vec`'s default, `next`-based collection path, not the specialized
hashbrown `fold`. The borrowed scan proof is reusable for that iterator
portion. Native vector first-element handling, allocation, size hints,
writes, length updates, and the repetition-sum loop still need their own
source-work coverage; value-order correspondence does not supply those charges.

The [existing raw comparison model](../../formal/rocq/rho_bridge/theories/GeneratedMapCoreSource.v)
uses one control relation with separate stored-payload and secondary-operand
types. Payload projections supply the optional secondary operand and original
repetition count. A supplied lead preserves the native constructor's initial
comparison. Map entrypoints specialize this relation to present secondary
values, unit repetitions, and an equal lead; their initialization and counter
restoration retain the original formulas. No second transition engine is kept.

The optional-secondary selector retains all native cases: two absent values
compare equal, absence precedes presence, and two present values either use
the original pointer-alias shortcut or request comparison of those exact
operands. Counter restoration uses the fetched original count only when its
remaining counter is zero. Its four-counter advancement is the existing
shared minimum/subtraction operation. Successful repeated-item construction
must still establish positive counts; arbitrary model projections do not
grant permission to construct a zero-count native item.

The [shared erasure model](../../formal/rocq/rho_bridge/theories/GeneratedMapCoreErasure.v)
transports this same control relation, including its suspended requests and
resumptions, between payload representations. Repetition counts must remain
equal, optional-secondary projection must commute with payload erasure, and
the original primary and secondary alias predicates must commute with their
operand maps. Supplied comparison answers, cursor positions, pending
destinations, totals, and remaining counts are unchanged. Existing Map
theorems specialize the shared proof to present secondary values and unit
counts; there is no second dialogue or comparison engine.

The [Bag source instantiation](../../formal/rocq/rho_bridge/theories/GeneratedBagCoreSource.v)
uses each original repetition count as the stored payload and an absent
secondary operand. It connects the actual repeated-item fields and original
ordered key/count pairs to the complete shared initial state, retaining the
stored-total lead separately from both repetition sums. Its callback transport
preserves the original primary pair and supplied answers through the existing
dialogue erasure proof.

An empty secondary type expresses the factory's absent field; eliminating
that type is not evidence about arbitrary native entries. The source connection
also uses the factory's actual `None` field, successful roster construction,
and valid original typed borrows and pointer casts. No new comparator,
canonicalization, callback executor, or comparison-result assumption is added.

These are source-model reuse prerequisites, not complete Bag execution
coverage. Erasure neither supplies a comparison-result oracle nor proves
termination or resource bounds. The actual typed Bag callback and event-cost
correspondence must still connect this relation to admitted native execution;
successful native repeated-item construction must separately justify its
positive-count precondition.

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

## Collection control-work coverage

The [control-work model](../../formal/rocq/rho_bridge/theories/GeneratedCollectionWorkCover.v)
reuses the original raw merge transitions. Successful copying preserves every
already-exhausted side, and an allocated target remains allocated through a
complete raw step. These invariants support grouping the native tail loops
without inventing a second executor or assuming a whole-call work bound.

A completed run executes the outer guard and comparison-readiness guard,
both tail loops including their terminal guards, and the run-end block. It
may also finish a pass and reset the next run. Let $`l`$ and $`r`$ be the
numbers of left and right tail copies, and let $`W_{\mathrm{run}}`$ denote
the control work of one completed run. The named control groups in
[`collection_cmp_pda.rs`](../../runtime/src/collection_cmp_pda.rs) give:

```math
W_{\mathrm{run}}\leq 7+2(l+r).
```

The final pass breaks without another outer guard. Scratch-buffer allocation
and disposal retain their separate existing allowance; requested term
comparisons retain their own typed coverage. These checked local laws are not
yet a factorization of every complete raw-step derivation, nor proof that a
whole native comparison has been prepaid.

## Weighted-run comparison results

The [weighted result model](../../formal/rocq/rho_bridge/theories/CollectionWeightedLexResults.v)
interprets each borrowed key/count pair as a repeated sequence only inside
the proof. The runtime keeps its existing compact rosters and remaining-count
cursors; it never allocates that expanded sequence. Its length is the
original repetition sum, not necessarily the bag's transported stored total.

Restoring a current entry's count leaves its remaining sequence unchanged.
When two positive current runs compare equal, the existing min/subtract
operation consumes the same number of repetitions from both sides. Removing
those equal-comparing prefixes preserves the lexicographic result even when
the original terms are distinct objects. A non-equal head decides the result
immediately. At exhaustion, the original repetition totals give the same
terminal ordering if both sides have consumed a common prefix length; the
whole-execution proof must derive that invariant from the transition laws.

Stored-total ordering remains a separate leading component. These result
laws do not change the requirement to construct both checked rosters before
testing that lead. They also do not supply sorting, absent-secondary request
protocols, owner scheduling, or whole-category source correspondence by
assumption. Those integrations reuse the existing comparison machinery and
retain their separate proof obligations.

## Normal owned cleanup boundaries

Borrowed iteration, consuming iteration, and destruction of a retained result
have different ownership effects. In the pinned native source, consuming
`RawIntoIter::next` forwards to its embedded `RawIter::next`, then moves the
returned bucket's record with `Bucket::read`. Its destructor continues that
same iterator through `RawIter::drop_elements`; it does not start another
table scan. Direct `RawTable` destruction instead calls
`RawTableInner::drop_inner_table`, which may construct a fresh iterator.

| Owner being released | Native scan during normal cleanup | Key and allocation effects |
|---|---|---|
| Borrowed comparison iterator | None | No key destruction or table release |
| Partially consumed `RawIntoIter` | Continue its existing cursor only if keys require destruction and stored entries remain | Destroy each remaining stored key once; release its allocation once if present |
| Retained reconstruction result | Fresh scan only if allocated, nonempty, and keys require destruction | Destroy each stored key once; release the allocation even when allocated but empty |

Let $`S`$ be the original sequence of occupied bucket positions, $`M`$ the
positions already moved out, and $`R`$ the positions remaining in the cursor.
Concatenation is denoted by $`\mathbin{+\!+}`$. A consuming prefix preserves
the exact occurrence partition:

```math
S=M\mathbin{+\!+}R.
```

When normal iterator destruction visits all remaining positions, the moved
prefix and destruction suffix belong to one scan with one initial group load.
After the final successful `next`, an empty suffix needs no terminal `next`
call during destruction. A previously constructed empty iterator has already
paid its initial load; an empty retained table destroyed directly never
constructs that iterator. These distinctions prevent charging an invented
second scan or omitting a real first scan.

The [owned-cursor composition](../../formal/rocq/rho_bridge/theories/NativeHashBagOwnedScan.v)
reuses the borrowed scan transitions. It proves that an actual consuming prefix
followed by a continuation is one original scan, preserves the exact pending
slot sequence, and partitions the original sequence at exhaustion. Both
segments share the existing historical event allowance, componentwise and
under any declared nonnegative cursor-event weights. This proof covers the
cursor events, not the separate ownership and destruction effects below.

One stored key is one owned occurrence, even when its count is zero or greater
than one. Equal key values or aliased child pointers do not merge ownership
receipts. Invoking a key destructor transfers to its complete, independently
admitted root-cleanup path; it is not a constant-time operation. Bucket reads,
ownership handoff, wrapper guards, and allocation release also require their
own source-backed accounting. The borrowed scan's event bound alone does not
cover those effects.

The [retained-table cleanup composition](../../formal/rocq/rho_bridge/theories/NativeHashBagRetainedCleanup.v)
selects the fresh scan using the native allocation, destructor, and entry-count
guards. It proves exact original-slot visitation and applies the historical
scan envelope. Its wrapper projection distinguishes destructor dispatch from
bucket moves: direct table cleanup invokes no `Bucket::read` and frees only
allocated tables. These are invocation counts, not constant destructor or
allocator costs.

Physical bucket order need not equal the reconstruction model's retained-list
order. The cleanup proof transfers existing full root receipts through a
permutation of retained ownership occurrences, then composes the existing
retained/discarded/pending partition. The native slot-to-owner association is
an explicit source obligation, not an equality-by-key or pointer shortcut.

`try_rebuild_entries_with` receives a `Vec<(T, usize)>`, not a consuming
`HashBag` iterator. A refused insertion leaves three distinct cleanup owners:
the current input key, the pending vector suffix, and the retained result bag.
Reuse the existing vector and root-occurrence cleanup laws for the first two;
the last uses the direct-table path above. Do not add a nonexistent incoming
hash-table scan to this interface.

Cleanup credit must be retained before mutation. In particular, a pending
insertion can enlarge the retained table, so observing its capacity after
growth is insufficient prepayment for cleanup. The prospective growth bound
and checked arithmetic must cover that future allocation before the original
native insertion runs. These are normal returned-error obligations, distinct
from arbitrary panic unwinding or physical allocator behavior.

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
