# ART01 -- Epoch-Scoped Intern Tables

## Overview

The hash-consing module provides the runtime infrastructure for the ART01
optimization: structural sharing of recursive term types via interning.
When the same term structure is constructed multiple times, hash-consing
returns an existing `Rc<T>` reference instead of allocating a new one. This
enables O(1) pointer-equality checks, reduces memory consumption through
sharing, and improves cache locality.

**Source:** `runtime/src/hash_consing.rs`

## Key Types

### `InternTable<T: Hash + Eq + Clone>`

A thread-local interning table that maps structural hashes to `Rc<T>` values.

```
InternTable<T>
  +-- epoch: u64               Current epoch (cleared on mismatch)
  +-- map: HashMap<u64, Vec<Rc<T>>>    Hash buckets with collision chains
```

**Invariants:**
- All `Rc<T>` values in a bucket share the same structural hash
- No two values in a bucket are structurally equal (`==`)
- The epoch matches the global `INTERN_EPOCH` (or the table is stale)

### `HashConsingAnalysis`

A summary result from compile-time analysis (not used at runtime, but defined
here for convenience as a shared type between the analysis and runtime crates):

```
HashConsingAnalysis
  +-- recursive_categories: Vec<String>     Categories with recursive fields
  +-- estimated_sharing: f64                Sharing ratio estimate (0.0 to 1.0)
  +-- recommended: bool                    true if categories exist and sharing > 0.1
```

## Algorithm: Interning

The `intern()` method performs a two-step lookup:

```
intern(value: T) -> Rc<T>
    1. check_epoch()           -- clear table if epoch has advanced
    2. hash = structural_hash(value)
    3. bucket = map[hash]      -- get or create collision chain
    4. for existing in bucket:
         if *existing == value:
           return Rc::clone(existing)     -- HIT: return shared reference
    5. rc = Rc::new(value)
       bucket.push(Rc::clone(rc))
       return rc                          -- MISS: insert and return new Rc
```

**Hash collisions** are handled by step 4: the bucket is a `Vec<Rc<T>>`, and
each entry is checked for structural equality. In practice, collisions are
rare (64-bit hash), so the linear scan over the bucket is O(1) amortized.

**Memory:** Each unique term is stored once. The `Rc` reference count tracks
how many AST nodes share the allocation. When the table is cleared (epoch
advancement), `Rc`s that are still referenced by the AST remain valid; only
the table's references are dropped.

## Epoch-Scoped Garbage Collection

The interning table uses an epoch mechanism to prevent unbounded growth
across Ascent evaluations:

```
  Epoch 0          Epoch 1          Epoch 2
  +--------+       +--------+       +--------+
  | table  |       | table  |       | table  |
  | {a,b,c}|  -->  | {d,e}  |  -->  | {f}    |
  +--------+       +--------+       +--------+
       ^                ^                ^
       |                |                |
  bump_intern_epoch  bump_intern_epoch
```

### Global Epoch Counter

```rust
thread_local! {
    static INTERN_EPOCH: Cell<u64> = const { Cell::new(0) };
}
```

- `bump_intern_epoch()` increments the counter (wrapping at u64::MAX)
- Called at the start of each `run_ascent_typed()` invocation, alongside
  `bump_bcg05_epoch()`

### Table-Local Epoch Check

Each `InternTable` stores its own `epoch` field. On every `intern()` call,
`check_epoch()` compares against the global counter:

```rust
fn check_epoch(&mut self) {
    let current = INTERN_EPOCH.with(|e| e.get());
    if self.epoch != current {
        self.epoch = current;
        self.map.clear();      // <-- drop all table references
    }
}
```

This lazy clearing means tables are only purged when actually accessed after
an epoch bump, avoiding unnecessary work for tables that are not used in a
given evaluation.

## Thread-Local Storage Pattern

The `define_intern_table!` macro creates a per-type, per-thread intern table:

```rust
define_intern_table!(INTERN_PROC, intern_proc, Proc);

// Expands to:
thread_local! {
    static INTERN_PROC: RefCell<InternTable<Proc>> =
        RefCell::new(InternTable::new());
}

fn intern_proc(value: Proc) -> Rc<Proc> {
    INTERN_PROC.with(|table| table.borrow_mut().intern(value))
}
```

Usage in generated code:

```rust
let term = Proc::PPar(intern_proc(left), intern_proc(right));
```

The `RefCell` provides interior mutability for the thread-local table.
Since Ascent evaluation is single-threaded (per-thread), the borrow is
always uncontested.

## Properties

### O(1) Equality

When hash-consing is enabled, equality between `Rc<T>` values can use
pointer comparison:

```rust
Rc::ptr_eq(&a, &b)   // O(1) instead of O(depth) structural comparison
```

This is correct because the interning invariant guarantees that structurally
equal terms share the same `Rc` allocation within an epoch.

### Sharing

Identical subterms are stored once. For languages with heavy subterm sharing
(e.g., `PPar(a, a)` where both children are identical), this reduces memory
by eliminating the duplicate allocation.

### Cache Locality

Fewer distinct allocations means the working set of pointers is smaller,
improving CPU cache hit rates during term traversal.

## Test Coverage

| Test | Property |
|------|----------|
| `test_intern_table_dedup` | Same value returns `Rc::ptr_eq` references |
| `test_intern_table_epoch_clear` | Epoch bump causes table clear on next access |
| `test_intern_table_hash_collision_handling` | Different values in same bucket remain distinct |
| `test_intern_table_empty` | Fresh table is empty |
| `test_intern_epoch_counter` | `bump_intern_epoch()` increments by 1 |
| `test_hash_consing_analysis` | `HashConsingAnalysis` recommendation logic |
| `prop_intern_dedup_invariant` | (proptest) `intern(x)` twice always `Rc::ptr_eq` |
| `prop_intern_distinct_values_distinct` | (proptest) `x != y` implies not `Rc::ptr_eq` |

## Integration

```
Compile Time                         Runtime
+-----------------------------------+  +----------------------------+
| hash_consing_analysis.rs          |  | hash_consing.rs            |
|   analyze_hash_consing(lang)      |  |   InternTable<T>           |
|   --> HashConsingReport           |  |   bump_intern_epoch()      |
|   --> ART01 gate decision         |  |   define_intern_table!     |
+-----------------------------------+  +----------------------------+
         |                                        ^
         |  (when ART01 enabled)                  |
         +--- generates intern calls  ----------->+
```

## Source References

- Runtime module: `runtime/src/hash_consing.rs` (290 lines)
- Compile-time analysis: `macros/src/gen/term_ops/hash_consing_analysis.rs`
- Epoch bump call site: generated `run_ascent_typed()` preamble
- Re-export: `runtime/src/lib.rs` (line 36)
