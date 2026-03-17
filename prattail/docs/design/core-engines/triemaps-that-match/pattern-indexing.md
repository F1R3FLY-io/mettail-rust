# Equation Pattern Trie: De Bruijn-Indexed Pattern Matching

PraTTaIL indexes equation and rewrite patterns in a PathMap trie using De Bruijn-canonicalized byte paths. This enables automatic alpha-equivalence grouping, fine-grained dependency stratification, subsumption detection, and bloom filter pre-check — all at compile time.

**Prerequisites:** [Foundations](foundations.md), [PathMap Overview](pathmap-overview.md)

---

## 1. Problem: Grouping Alpha-Equivalent Patterns

When the `language!` macro processes user-defined equations and rewrites, it needs to:

1. **Group alpha-equivalent LHS patterns** — equations `f(x,y) = g(x,y)` and `f(a,b) = g(a,b)` have the same LHS up to renaming
2. **Compute dependency groups** — equations sharing constructors must be in the same stratum for correct Datalog evaluation
3. **Detect subsumption** — if pattern `P` matches every term that `Q` matches, rule `Q` may be redundant
4. **Reject quickly** — when checking whether a term matches any pattern, reject non-matching terms in O(1) before expensive trie descent

The pattern trie solves all four problems using a single PathMap indexed by De Bruijn-encoded bytes.

---

## 2. De Bruijn Byte Encoding

The encoding is defined in `macros/src/logic/pattern_codec.rs`. Each pattern is serialized to a byte sequence where alpha-equivalent patterns produce identical bytes.

### Tag Byte Layout (MORK-Compatible 2-Bit Prefix Scheme)

```text
 Prefix   Range          Tag             Meaning
 ──────   ──────────     ────────        ─────────────────────────────────
 0b00     0x00-0x3F      Arity(a)        Constructor application with a children
 0b01     0x40-0x4B      Extension       PraTTaIL-specific tags (see below)
 0b10     0x80-0xBF      VarRef(i)       Reference to i-th introduced variable
 0b11     0xC0           NewVar          Introduce a fresh variable
 0b11     0xC1-0xFE      SymbolSize(s)   Next s bytes are a constructor name
 0b11     0xFF           ExtTag          Reserved
```

### PraTTaIL Extension Tags (0x40-0x4B)

| Byte | Constant | Meaning |
|------|----------|---------|
| `0x40` | `TAG_COLLECTION_HASHBAG` | HashBag collection |
| `0x41` | `TAG_COLLECTION_HASHSET` | HashSet collection |
| `0x42` | `TAG_COLLECTION_VEC` | Vec (ordered) collection |
| `0x43` | `TAG_COLLECTION_INFER` | Inferred collection type |
| `0x44` | `TAG_REST_VAR` | Rest variable in collection |
| `0x45` | `TAG_NO_REST` | No rest variable |
| `0x46` | `TAG_MAP` | Map combinator |
| `0x47` | `TAG_ZIP` | Zip combinator |
| `0x48` | `TAG_LAMBDA` | Lambda abstraction |
| `0x49` | `TAG_MULTI_LAMBDA` | Multi-binder lambda |
| `0x4A` | `TAG_SUBST` | Explicit substitution |
| `0x4B` | `TAG_MULTI_SUBST` | Multi-variable substitution |

### Encoding Examples

**Constructor application** `Add(x, y)`:

```text
Bytes: [0x02, 0xC3, 'A', 'd', 'd', 0xC0, 0xC0]
         │      │                     │     │
         │      │                     │     └─ NewVar (y → slot 1)
         │      │                     └─ NewVar (x → slot 0)
         │      └─ SymbolSize(3): next 3 bytes = "Add"
         └─ Arity(2): 2 children
```

**Alpha-equivalent** `Add(a, b)` produces identical bytes:

```text
Bytes: [0x02, 0xC3, 'A', 'd', 'd', 0xC0, 0xC0]
```

**Repeated variable** `Add(x, x)`:

```text
Bytes: [0x02, 0xC3, 'A', 'd', 'd', 0xC0, 0x80]
         │                                  │     │
         │                                  │     └─ VarRef(0): x was slot 0
         │                                  └─ NewVar (x → slot 0)
         └─ Arity(2)
```

Note: `Add(x, x)` ≠ `Add(x, y)` because `0x80` (VarRef) ≠ `0xC0` (NewVar).

### Binder Handling

Lambda patterns use `introduce_binder()` and `restore_binder()` for correct scoping:

```rust
PatternTerm::Lambda { binder, body } => {
    buf.push(TAG_LAMBDA);
    let name = binder.to_string();
    let (slot, prev) = env.introduce_binder(&name);
    buf.push(slot);
    encode_pattern(body, env, buf);
    env.restore_binder(&name, prev);
}
```

This ensures that `λx.f(x)` and `λy.f(y)` produce identical bytes (the binder variable is always slot `next_slot`, regardless of name).

### Collection Canonicalization

Unordered collections (HashBag, HashSet, inferred) are canonicalized by encoding each element into a temporary buffer, sorting the buffers lexicographically, then concatenating:

```text
{b, a} → encode(b), encode(a) → sort → [encode(a), encode(b)]
```

This ensures `{x, y}` and `{y, x}` produce the same bytes when the collection type is unordered.

---

## 3. PatternIndex

The `PatternIndex` struct (`pattern_trie.rs:94-107`) ties together the trie, bloom filter, and metadata:

```rust
pub struct PatternIndex {
    pub lhs_trie: PathMap<RuleIdSet>,
    pub rhs_trie: PathMap<RuleIdSet>,
    pub lhs_bloom: BloomFilter,
    pub constructor_sets: HashMap<RuleId, HashSet<String>>,
    pub lhs_bytes: HashMap<RuleId, Vec<u8>>,
    pub rule_count: usize,
}
```

| Field | Purpose |
|-------|---------|
| `lhs_trie` | LHS pattern bytes → rule IDs (alpha-equivalence grouping) |
| `rhs_trie` | RHS pattern bytes → rule IDs (for overlap analysis) |
| `lhs_bloom` | O(1) negative rejection before trie descent |
| `constructor_sets` | Per-rule set of constructor labels (for dependency groups) |
| `lhs_bytes` | Per-rule raw De Bruijn bytes (for subsumption and diagnostics) |

### Building

`PatternIndex::build()` (`pattern_trie.rs:111-211`) processes all equations and rewrites:

```text
For each equation/rewrite:
  1. Encode LHS pattern → lhs_bytes (via pattern_to_debruijn_bytes)
  2. Encode RHS pattern → rhs_bytes
  3. Insert lhs_bytes into lhs_bloom
  4. Insert lhs_bytes → RuleIdSet into lhs_trie (join if path exists)
  5. Insert rhs_bytes → RuleIdSet into rhs_trie
  6. Collect constructor labels from both sides
```

If two rules have alpha-equivalent LHS patterns, they map to the same byte path. The `pjoin` operation on `RuleIdSet` merges their rule ID sets at that trie node.

---

## 4. RuleIdSet Lattice

`RuleIdSet` (`pattern_trie.rs:44-83`) wraps `Vec<RuleId>` with lattice operations:

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuleIdSet(pub Vec<RuleId>);
```

| Operation | Semantics |
|-----------|-----------|
| `pjoin(A, B)` | Sorted set union of rule IDs |
| `pmeet(A, B)` | Set intersection of rule IDs |

Identity detection avoids allocation when the result equals an operand:

```rust
fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
    let mut merged = self.0.clone();
    for id in &other.0 {
        if !merged.contains(id) {
            merged.push(*id);
        }
    }
    merged.sort();
    if merged == self.0 { AlgebraicResult::Identity(SELF_IDENT) }
    else if merged == other.0 { AlgebraicResult::Identity(COUNTER_IDENT) }
    else { AlgebraicResult::Element(RuleIdSet(merged)) }
}
```

---

## 5. Fine-Grained Dependency Groups

`compute_fine_dependency_groups()` (`pattern_trie.rs:265-311`) uses union-find to partition rules into groups that share constructors:

### Algorithm

```text
1. For each rule, collect its set of constructor labels
2. Create a union-find over all rules
3. For each constructor label:
   a. Find the first rule that references it
   b. Union that rule with every other rule that references the same label
4. Collect connected components as dependency groups
```

### Why This Matters

Rules in the same dependency group interact during Datalog evaluation — they may fire derivations that trigger each other. Rules in different groups are independent and can be evaluated in any order. This enables:

- **Stratum partitioning**: Independent groups can be placed in separate strata
- **Dead rule detection**: A group with no reachable seed terms has no live rules
- **Parallelism**: Independent groups can be evaluated concurrently

---

## 6. Subsumption Detection

`detect_subsumption()` (`pattern_trie.rs:362-408`) identifies cases where one pattern is strictly more general than another:

### Definition

> Pattern `G` **subsumes** pattern `S` if `G` matches every term that `S` matches.

In De Bruijn encoding, this corresponds to `G` having a variable tag where `S` has concrete structure, while agreeing on all other positions.

### Examples

| General | Specific | Subsumes? | Reason |
|---------|----------|-----------|--------|
| `f(x)` | `f(Add(a,b))` | Yes | `x` matches `Add(a,b)` |
| `x` | anything | Yes | `x` matches everything |
| `f(x,y)` | `f(x,x)` | No | `y` is fresh, `x` is repeated — different constraints |
| `f(x)` | `g(x)` | No | Different constructors |

### Algorithm

`is_pattern_generalization()` walks both byte sequences in parallel:

1. If general has a variable (`NewVar`/`VarRef`) and specific has structure → generalization at this position
2. If both have the same constructor → recurse on children, require at least one generalization
3. If constructors differ → not a generalization
4. Single `NewVar` subsumes everything

This is a conservative (sound but incomplete) check. It catches the common cases shown above.

---

## 7. Bloom Filter Pre-Check

The bloom filter (`macros/src/logic/bloom_filter.rs`) provides O(1) negative rejection before PathMap descent:

| Property | Value |
|----------|-------|
| Hash functions | 3 (FxHasher with seed) |
| Bits per element | ~10 (target ~1% false positive rate) |
| Storage | `Vec<u64>` bit array |
| False positives | Possible (requires full trie check) |
| False negatives | **Never** (guaranteed correct rejection) |

The bloom filter is inserted with each LHS pattern's byte encoding during index construction:

```rust
lhs_bloom.insert_bytes(&lhs_b);
```

At query time, `might_contain_bytes()` returns `false` if the pattern is definitely not in the index, avoiding the O(k) trie descent entirely.

### Additional Usage

Beyond the pattern index, the bloom filter is also used at codegen time by congruence rule generators to:
1. Track which constructor labels participate in equality/rewrite congruence groups
2. Build exact `matches!()` guards on constructor discriminants
3. Eliminate O(|cat|²) cross-constructor pairs in equality congruence

---

## 8. Connection to the Paper

The pattern trie is PraTTaIL's closest implementation of the paper's matching trie concept:

| Paper concept | PatternIndex implementation |
|--------------|---------------------------|
| `PatExpr` (patterns with variables) | `Pattern` with `PatternTerm::Var` |
| `PatKeys` (stored patterns) | `lhs_trie: PathMap<RuleIdSet>` |
| `MatchME` (matching triemap) | Read zipper traversal with wildcard matching |
| `mm_pvar` (pattern variable field) | `NewVar` (0xC0) and `VarRef` (0x80\|slot) tags |
| `matchPatVarE` (pattern variable matching) | `is_pattern_generalization()` |
| `unionPatME` (merging pattern tries) | `RuleIdSet::pjoin()` |
| `DBEnv` (De Bruijn environment) | `EncodingEnv` with `var_slots` + `next_slot` |

The key difference: the paper's matching trie is a runtime data structure for looking up stored patterns against concrete terms. PraTTaIL's pattern trie is a compile-time analysis tool for grouping, stratifying, and detecting subsumption among user-defined equation patterns.

---

## Key Source Files

| File | Lines | Role |
|------|-------|------|
| `macros/src/logic/pattern_codec.rs` | ~400 | De Bruijn byte encoding |
| `macros/src/logic/pattern_trie.rs` | ~500 | PatternIndex, dependency groups, alpha-equivalence, subsumption |
| `macros/src/logic/bloom_filter.rs` | ~140 | Bloom filter for negative rejection |

---

**Next:** [Grammar Algebra](grammar-algebra.md) — lattice operations for grammar composition analysis.
