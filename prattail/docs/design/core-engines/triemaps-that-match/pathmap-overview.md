# PathMap Data Structure

PathMap is the persistent radix-256 trie that underpins PraTTaIL's structural indexing. It provides O(k) lookup, O(1) copy-on-write forking, and lattice algebra operations that enable grammar composition analysis.

**Prerequisites:** [Foundations](foundations.md)

---

## 1. What PathMap Is

PathMap is an **external crate** (`/home/dylon/Workspace/f1r3fly.io/PathMap/`) providing a generic persistent trie keyed by byte paths. Its core properties:

| Property | Value |
|----------|-------|
| Branching factor | 256 (one child slot per byte value) |
| Key type | `&[u8]` (arbitrary byte sequences) |
| Value type | Generic `V: Lattice` |
| Persistence | Arc-based structural sharing (copy-on-write) |
| Equality | Hash-consed O(1) pointer equality |
| Thread safety | `Send + Sync` via `Arc` |

Unlike a HashMap (which hashes the entire key) or a BTreeMap (which compares keys lexicographically), PathMap **decomposes** keys into their byte structure. This decomposition is what enables matching lookup and prefix sharing.

### Core API

```rust
// Creation
let mut map = PathMap::<V>::new();

// Insertion (creates path if needed, sets value at leaf)
map.insert(&bytes, value);
map.set_val_at(&bytes, value);

// Lookup
let val: Option<&V> = map.get(&bytes);
let val: Option<&mut V> = map.get_mut(&bytes);

// Iteration (via zipper)
let rz = map.read_zipper();
while rz.to_next_val() {
    let val: &V = rz.val().unwrap();
}

// Lattice operations
let joined  = map_a.join(&map_b);     // ⊔ union
let met     = map_a.meet(&map_b);     // ⊓ intersection
let diff    = map_a.subtract(&map_b); // ∖ difference

// Statistics
let count: usize = map.val_count();
```

---

## 2. Lattice Trait Hierarchy

PathMap's algebraic operations require the value type `V` to implement lattice traits defined in `pathmap::ring`:

### `Lattice` Trait

```rust
pub trait Lattice {
    /// Join (⊔): least upper bound / merge / union.
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self>;

    /// Meet (⊓): greatest lower bound / intersection.
    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self>;
}
```

### `DistributiveLattice` Trait

```rust
pub trait DistributiveLattice: Lattice {
    /// Subtract (∖): relative complement / difference.
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self>;
}
```

### `AlgebraicResult<V>` Enum

The return type of lattice operations uses a three-variant enum to avoid unnecessary allocation:

```rust
pub enum AlgebraicResult<V> {
    /// A new element was computed.
    Element(V),
    /// The result is identical to one of the operands (no allocation needed).
    /// `Identity(SELF_IDENT)` = self, `Identity(COUNTER_IDENT)` = other.
    Identity(usize),
    /// The operation produced the bottom element (empty/none).
    None,
}
```

This is a critical optimization: when `a ⊔ b = a` (because `b ⊆ a`), the result is `Identity(SELF_IDENT)` — no new value is allocated. PathMap propagates this identity upward through the trie structure, avoiding node allocation when sub-trees are unchanged.

### Algebraic Laws

The lattice operations satisfy the standard laws:

| Law | Formula | Verified by |
|-----|---------|-------------|
| Commutativity | `a ⊔ b = b ⊔ a`, `a ⊓ b = b ⊓ a` | PathMap unit tests |
| Associativity | `(a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)` | PathMap unit tests |
| Idempotence | `a ⊔ a = a`, `a ⊓ a = a` | Identity detection |
| Absorption | `a ⊔ (a ⊓ b) = a` | Follows from above |
| Distributivity | `a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)` | DistributiveLattice bound |

---

## 3. Lattice Implementations in PraTTaIL

PraTTaIL defines two `Lattice` implementations for its domain types:

### `DecisionAction` (Parse Dispatch)

Defined in `prattail/src/decision_tree.rs:139-227`:

| Operation | Semantics |
|-----------|-----------|
| `pjoin` | Merge rule candidates: `Commit ⊔ Commit → Ambiguous`, `Ambiguous ⊔ X → extend candidates` |
| `pmeet` | Keep only shared rule labels (set intersection on rule_labels) |
| `psubtract` | Remove rules present in the other operand (set difference on rule_labels) |

The lattice on `DecisionAction` has a natural interpretation:
- **Bottom** (⊥): `AlgebraicResult::None` — no rule dispatches here
- **Commit**: a single rule — the deterministic case
- **Ambiguous**: multiple rules — the parser must try alternatives

Merging two `Commit` values with different rules produces an `Ambiguous`. This is exactly the grammar composition semantics: combining two grammars at a dispatch point where both have rules creates an ambiguity.

### `RuleIdSet` (Pattern Index)

Defined in `macros/src/logic/pattern_trie.rs:47-83`:

| Operation | Semantics |
|-----------|-----------|
| `pjoin` | Set union of rule IDs (merge-sort deduplication) |
| `pmeet` | Set intersection of rule IDs |

This models the equation index: two patterns at the same byte path share a trie node, and their rule ID sets are joined. Alpha-equivalent patterns automatically merge because they produce identical byte paths.

---

## 4. Zipper API

PathMap provides read and write zippers for efficient traversal without allocating intermediate collections:

### Read Zipper

```rust
let mut rz = map.read_zipper();

// Navigate to next value in depth-first order
while rz.to_next_val() {
    let value: &V = rz.val().unwrap();
    // ... process value
}
```

Used by `find_alpha_equivalent_groups()` (`pattern_trie.rs:323-337`) to iterate all multi-rule trie nodes:

```rust
pub fn find_alpha_equivalent_groups(index: &PatternIndex) -> Vec<Vec<RuleId>> {
    let mut rz = index.lhs_trie.read_zipper();
    let mut groups = Vec::new();
    while rz.to_next_val() {
        if let Some(rule_set) = rz.val() {
            if rule_set.0.len() >= 2 {
                groups.push(rule_set.0.clone());
            }
        }
    }
    // ...
}
```

### Write Zipper

Write zippers enable modification during traversal:

```rust
let mut wz = map.write_zipper();
wz.descend_to(&path);
wz.set_val(new_value);
```

### Traits

| Trait | Purpose |
|-------|---------|
| `ZipperIteration` | Navigation: `to_next_val()`, `descend_to()`, `ascend()` |
| `ZipperValues` | Value access: `val()`, `set_val()`, `take_val()` |

---

## 5. Why PathMap (Not HashMap, BTreeMap, etc.)

### Matching Lookup is Impossible with Hash/BST

As noted in the paper (§2.4), hash maps and balanced trees cannot perform matching lookup:

- **HashMap**: Hash functions are one-way. Given `hash(f(x, y))` where `x` is a pattern variable, there is no way to enumerate all `hash(f(a, b))` for concrete `a`, `b`.
- **BTreeMap**: The total order on keys means `f(x, y) < f(a, b)` must be deterministic, but a pattern variable `x` has no fixed position in the order.

### Prefix Sharing

When two keys share a common prefix, PathMap shares the trie nodes for that prefix. This is crucial for decision trees where many parse rules share the same leading terminals:

```text
Grammar rules:
  If := "if" Proc "then" Proc "else" Proc
  IfThen := "if" Proc "then" Proc

Trie (shared "if" prefix):
  root
   └─ 0x03 ("if")
       ├─ [NonTerminal(Proc)] → segment 1
       │   └─ 0x04 ("then")
       │       ├─ [NonTerminal(Proc)] → Commit(IfThen)
       │       └─ [NonTerminal(Proc)] → segment 2
       │           └─ 0x05 ("else") → ... → Commit(If)
       ...
```

Without prefix sharing, each rule would need its own copy of the shared prefix nodes.

### Algebraic Composition

The lattice operations enable grammar analysis that would require O(n²) pairwise comparisons with other data structures. PathMap's `meet`/`join`/`subtract` traverse both tries simultaneously in O(min(m,n)) time, where m and n are the number of trie nodes — not the number of rules.

---

## 6. PathMap's Role in PraTTaIL

PathMap appears in two distinct contexts:

| Context | Import site | PathMap type | Purpose |
|---------|-------------|-------------|---------|
| **Decision trees** | `decision_tree.rs:32-33` | `PathMap<DecisionAction>` | Parse dispatch: byte-encoded token prefixes → rule actions |
| **Pattern index** | `pattern_trie.rs:22-24` | `PathMap<RuleIdSet>` | Equation stratification: De Bruijn bytes → rule groups |

Both contexts use the same underlying data structure with different value types. The decision tree uses `DecisionAction` (which distinguishes deterministic vs. ambiguous dispatch), while the pattern index uses `RuleIdSet` (which tracks which rules share a pattern).

Neither context stores a runtime PathMap in the generated code. Instead, the tries are built during macro expansion, analyzed for their properties (dispatch determinism, alpha-equivalence groups, subsumption), and the results are codegen'd as match arms and optimized Ascent rules.

---

**Next:** [Decision Trees](decision-trees.md) — how PathMap tries power parse dispatch.
