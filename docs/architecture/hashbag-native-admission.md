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
| `vendor/hashbrown-0.17.1/src/raw.rs` | `0c8ad353ba95817e72b0a8fea48fa2599099ea3def374f254ab6402a9c468d22` |
| `vendor/hashbrown-0.17.1/src/map.rs` | `b79497ce537ffc5ed4f8f3399434b9216c01e7927fdc434fee190e9e9ce2abb0` |
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

The proposed metadata preserves the stronger boundary invariants:

```math
C(B)=I+D+G,\qquad C(B)\leq H.
```

Valid allocated sizes are powers of two starting at four. Their exact capacity
formula gives the following target bound; the singleton is handled separately:

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
establishes the exact capacity arithmetic and singleton initialization laws.
Those facts alone do not establish mutation preservation, scan coverage, or
prepayment of a future resize.

## Mutation and observation order

Reserve/rehash/resize and the final lookup result are distinct steps. In
particular, `HashMap::insert` calls `find_or_find_insert_index`, whose
`reserve(1)` precedes searching (`raw.rs`, lines 1120–1143; `map.rs`, around
line 1806). Replacing an existing binding key can therefore resize the table
without increasing its entry count. By contrast, `HashMap::entry` searches
first (`map.rs`, around line 1207), as used by `insert` and `insert_n`.

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

## Remaining concrete coverage

The extent invariant is one input to admission, not the complete allowance.
The next refinements must establish:

1. Control-group scanning, yielded entries, terminal probes, and consuming
   cleanup. `RawIterRange` loads its first group during construction and then
   advances monotonically through groups (`raw.rs`, lines 3558–3673). Small
   tables have padded control bytes; count those boundaries explicitly.
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
