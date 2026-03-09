# ART04: Bloom Filter Pre-Check

**Source**: [`macros/src/logic/bloom_filter.rs`](../../src/logic/bloom_filter.rs)

## 1. Overview / Purpose

The bloom filter module provides a probabilistic data structure used at
*codegen time* (macro expansion) to construct fast discriminant pre-check
guards for congruence rules. The bloom filter guarantees zero false negatives:
if a constructor label is in the filter, `might_contain_str()` always returns
`true`. False positives are possible but bounded below ~1%.

The key insight is that congruence rules (both equality and rewrite) apply
only to constructors that participate in congruence groups. Non-participating
constructors would fall through to the `_ => {}` arm of the TLS pool match,
doing zero useful work. By generating a `matches!()` guard on constructor
discriminants, non-participating constructors are rejected with a single
integer comparison before the more expensive pool match evaluation begins.

At codegen time, the full set of participating constructors is known, so the
generated `matches!()` guard is **exact** (no false positives). The bloom
filter serves as a codegen-time verification tool ensuring no constructors
are accidentally omitted (zero false negatives assertion).

## 2. Architecture and Data Flow

```
 Congruence Group Analysis (equations.rs / congruence.rs)
     |
     v
 For each (category, field_types) group:
     |
     +---> BloomFilter::new(group_size)
     |         |
     |         v
     +---> bloom.insert_str(constructor_label)  (for each ctor in group)
     |         |
     |         v
     +---> debug_assert!(bloom.might_contain_str(label))  // verify no FN
     |         |
     |         v
     +---> Generate matches!() guard from known constructor set
     |
     v
 TokenStream: if matches!(s, Cat::A(..) | Cat::B(..) | ...)
```

### Integration Points

The bloom filter is consumed by two modules:

1. **`equations.rs`** -- Equality congruence (G37 diagnostic):
   - Per-category bloom of constructors participating in eq congruence groups
   - Generates `std::mem::discriminant(s) == std::mem::discriminant(t)` guard
   - Generates `matches!(s, ...)` guard when group is a strict subset of category

2. **`congruence.rs`** -- Rewrite congruence (G38 diagnostic):
   - Per-group bloom of constructors with simple congruence entries
   - Generates `matches!(lhs, ...)` guard for consolidated congruence rules

## 3. Key Types and Functions

### `BloomFilter`

```rust
pub struct BloomFilter {
    bits: Vec<u64>,     // Bit vector stored as u64 chunks
    bit_count: usize,   // Total bits in the filter
    hash_count: usize,  // Number of hash functions (always 3)
}
```

### Public API

| Method                  | Returns    | Purpose                                    |
|-------------------------|------------|--------------------------------------------|
| `new(expected_elements)`| `Self`     | Create filter with ~1.2 bytes/element       |
| `insert_bytes(bytes)`   | `()`       | Add raw bytes to filter                     |
| `insert_str(s)`         | `()`       | Add string to filter (convenience)          |
| `might_contain_bytes(bytes)` | `bool` | Fast rejection test (false = definitely not)|
| `might_contain_str(s)`  | `bool`     | String rejection test (convenience)         |
| `occupancy()`           | `usize`    | Count of set bits (rough fill measure)      |

### Internal

| Method                       | Purpose                                          |
|------------------------------|--------------------------------------------------|
| `hash_with_seed(bytes, seed)`| FxHash with seed for k-hash simulation            |

## 4. Algorithm Description

### Construction

```
BloomFilter::new(n):
    bit_count = max(n * 10, 64)           // 10 bits per element
    chunk_count = ceil(bit_count / 64)
    bits = vec![0u64; chunk_count]
    hash_count = 3                        // optimal for 10 bits/element
```

### Insertion

```
insert_bytes(bytes):
    for seed in 0..3:
        hash = FxHash(seed ++ bytes)
        bit_index = hash % bit_count
        bits[bit_index / 64] |= (1 << (bit_index % 64))
```

### Query

```
might_contain_bytes(bytes) -> bool:
    for seed in 0..3:
        hash = FxHash(seed ++ bytes)
        bit_index = hash % bit_count
        if bits[bit_index / 64] & (1 << (bit_index % 64)) == 0:
            return false     // definitely NOT in set
    return true              // might be in set
```

### False Positive Rate

With 3 hash functions and 10 bits per element, the theoretical false positive
rate is approximately:

  FPR = (1 - e^(-kn/m))^k = (1 - e^(-3n/(10n)))^3 = (1 - e^(-0.3))^3 ~= 1.5%

The proptest in the test suite verifies the observed FPR stays below 10%
(generous bound accommodating hash distribution variance).

## 5. Generated Code Patterns

### Equality Congruence (equations.rs) -- Before ART04:

```
eq_proc(s.clone(), t.clone()) <--
    proc(s),
    proc(t),
    for (s_f0, t_f0) in POOL_PROC_EQ_CONG_0.take_fill(s, t),
    eq_name(s_f0, t_f0);
```

This evaluates the pool match for every (s, t) pair in `proc x proc`,
including cross-constructor pairs like (PDrop, PPar) that can never match.

### Equality Congruence -- After ART04:

```
eq_proc(s.clone(), t.clone()) <--
    proc(s),
    proc(t),
    if std::mem::discriminant(s) == std::mem::discriminant(t),  // O(1) int cmp
    if matches!(s, Proc::PDrop(..) | Proc::POutput(..)),       // subset guard
    for (s_f0, t_f0) in POOL_PROC_EQ_CONG_0.take_fill(s, t),
    eq_name(s_f0, t_f0);
```

The `discriminant` guard eliminates all cross-constructor pairs (O(|cat|^2) to
O(|cat|) worst case). The `matches!()` guard further eliminates constructors
that don't participate in this congruence group.

### Rewrite Congruence (congruence.rs) -- Before ART04:

```
rw_proc(lhs.clone(), rebuilt) <--
    proc(lhs),
    for (field_val, vi) in POOL_PROC_SCONG_NAME.take_fill(lhs),
    rw_name(field_val, t);
```

### Rewrite Congruence -- After ART04:

```
rw_proc(lhs.clone(), rebuilt) <--
    proc(lhs),
    if matches!(lhs, Proc::PDrop(..) | Proc::POutput(..)),  // exact guard
    for (field_val, vi) in POOL_PROC_SCONG_NAME.take_fill(lhs),
    rw_name(field_val, t);
```

### Codegen-Time Verification

At macro expansion time, the bloom filter is constructed and verified:

```rust
let mut bloom = BloomFilter::new(by_constructor.len().max(1));
for label in &participating_labels {
    bloom.insert_str(&label.to_string());
}
debug_assert!(
    participating_labels.iter().all(|l| bloom.might_contain_str(&l.to_string())),
    "A-RT04: bloom filter false negative detected"
);
```

This `debug_assert!` fires during development builds if the bloom filter would
produce a false negative, catching bugs in the constructor tracking logic.

## 6. Integration with Pipeline

The bloom filter is constructed and consumed entirely within the macro expansion
phase. It does not appear in the generated Ascent code -- only the derived
`matches!()` and `discriminant` guards are emitted.

### In `equations.rs::generate_congruence_rules()`:

1. Build per-category `BloomFilter` from constructor labels in each group
2. Verify zero false negatives via `debug_assert!`
3. Generate `discriminant` equality guard (always)
4. Generate `matches!()` guard if group is a strict subset of category
5. Emit G37 diagnostic with bloom filter occupancy

### In `congruence.rs::generate_consolidated_simple_congruence()`:

1. Build `BloomFilter` from participating constructor labels
2. Verify zero false negatives via `debug_assert!`
3. Generate `matches!()` guard from the known constructor set
4. Emit G38 diagnostic with guard count

## 7. Diagnostic Emissions

| Lint ID | Name                               | Severity | Trigger                           |
|---------|------------------------------------|----------|-----------------------------------|
| G37     | `bloom-filter-eq-congruence-guard` | Note     | Equality congruence groups guarded |
| G38     | `bloom-filter-rw-congruence-guard` | Note     | Rewrite congruence groups guarded |

G37 includes per-category bloom filter occupancy in the hint:
```
per-category bloom filter occupancy: [Proc: 12 bits set, Name: 4 bits set]
```

G38 includes the total constructor count participating:
```
3 rewrite congruence group(s) guarded by discriminant pre-check (A-RT04) --
8 constructor(s) participate; non-participating terms skipped before pool evaluation
```

## 8. Test Coverage

The module includes 8 tests (6 unit + 2 proptest):

| Test                                | What it verifies                        |
|-------------------------------------|-----------------------------------------|
| `test_bloom_filter_basic`           | Insert and query two strings            |
| `test_bloom_filter_no_false_negatives` | 100 items all query true             |
| `test_bloom_filter_bytes`           | Raw byte insertion and query            |
| `test_bloom_filter_str_convenience` | String convenience wrappers             |
| `test_bloom_filter_str_no_false_negatives` | 25 constructor names all query true |
| `test_bloom_filter_occupancy`       | Occupancy count increases after insert  |
| `prop_no_false_negatives`           | Proptest: N u64 items, all query true   |
| `prop_false_positive_rate_bound`    | Proptest: FPR < 10% with 100 inserts, 1000 probes |

## 9. Source References

- **Primary source**: [`macros/src/logic/bloom_filter.rs`](../../src/logic/bloom_filter.rs) (~258 lines)
- **Equality congruence consumer**: [`macros/src/logic/equations.rs`](../../src/logic/equations.rs), `generate_congruence_rules()`
- **Rewrite congruence consumer**: [`macros/src/logic/congruence.rs`](../../src/logic/congruence.rs), `generate_consolidated_simple_congruence()`
- **Origin**: Adapted from `libdictenstein`'s `bloom_filter.rs` implementation

## 10. Cross-References

- [congruence-closure.md](congruence-closure.md) -- rewrite congruence ART04 integration
- [equation-system.md](equation-system.md) -- equality congruence ART04 integration
- [`docs/design/codegen-optimization-catalog.md`](../../../docs/design/codegen-optimization-catalog.md) -- ART04 catalog entry
