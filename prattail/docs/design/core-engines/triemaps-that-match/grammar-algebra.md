# Grammar Algebra: Lattice Operations for Composition Analysis

PraTTaIL exploits PathMap's lattice operations to perform algebraic analysis of grammar composition. By treating decision trees as lattice elements, questions about grammar merging, overlap, and difference reduce to single-pass trie operations.

**Prerequisites:** [PathMap Overview](pathmap-overview.md), [Decision Trees](decision-trees.md)

---

## 1. Three Questions About Grammar Composition

When composing two grammars (e.g., a base language and an extension), three questions arise:

| Question | Operation | PathMap method |
|----------|-----------|---------------|
| Which rules do both grammars share? | **Meet** (⊓) | `tree_a.meet(&tree_b)` |
| Which rules are unique to each grammar? | **Subtract** (∖) | `tree_a.subtract(&tree_b)` |
| Does merging introduce new ambiguities? | **Join** (⊔) | `tree_a.join(&tree_b)` |

All three questions are answered by `composition_trie_analysis()` (`decision_tree.rs:2054-2104`) in a single analysis pass:

```rust
pub fn composition_trie_analysis(
    tree_a: &CategoryDecisionTree,
    tree_b: &CategoryDecisionTree,
) -> CompositionTrieReport {
    let common   = tree_a.segments[0].meet(&tree_b.segments[0]);    // ⊓
    let unique_a = tree_a.segments[0].subtract(&tree_b.segments[0]); // A ∖ B
    let unique_b = tree_b.segments[0].subtract(&tree_a.segments[0]); // B ∖ A
    let merged   = tree_a.segments[0].join(&tree_b.segments[0]);     // ⊔
    // ... count values in each result
}
```

---

## 2. DecisionAction Lattice Operations

### Join (⊔) — Merge

Combines two dispatch points by collecting all rule candidates:

```text
Commit("If") ⊔ Commit("Let")  =  Ambiguous{If, Let}
Ambiguous{A,B} ⊔ Commit("C")  =  Ambiguous{A, B, C}
Commit("X") ⊔ Commit("X")     =  Ambiguous{X, X}  (deduplicated → Commit("X"))
```

When two grammars both dispatch on the same token prefix, join reveals whether they conflict. A `Commit` result means they agree; `Ambiguous` means the parser will need disambiguation.

### Meet (⊓) — Intersect

Keeps only rules shared by both operands:

```text
Commit("If") ⊓ Commit("If")   =  Commit("If")        (same rule → keep)
Commit("If") ⊓ Commit("Let")  =  None                  (no overlap)
Ambiguous{A,B,C} ⊓ Ambiguous{B,C,D}  =  Ambiguous{B,C}  (shared rules)
```

The result of `A.meet(&B)` is the set of parse dispatch paths that exist identically in both grammars.

### Subtract (∖) — Difference

Removes rules present in the other grammar:

```text
Ambiguous{A,B,C} ∖ Ambiguous{A,B}  =  Commit("C")      (only C remains)
Commit("If") ∖ Commit("If")          =  None              (nothing left)
Commit("If") ∖ Commit("Let")         =  Commit("If")     (no overlap)
```

The result of `A.subtract(&B)` is the rules unique to grammar A — the "extension" that A provides beyond B.

---

## 3. CompositionTrieReport

The analysis returns a compact summary:

```rust
pub struct CompositionTrieReport {
    pub common_rules: usize,     // |A ⊓ B|
    pub unique_a: usize,         // |A ∖ B|
    pub unique_b: usize,         // |B ∖ A|
    pub new_ambiguities: usize,  // Ambiguous nodes in A ⊔ B
}
```

### Interpretation

| Scenario | common | unique_a | unique_b | ambiguities |
|----------|--------|----------|----------|-------------|
| Identical grammars | N | 0 | 0 | 0 |
| Disjoint grammars | 0 | M | N | 0 |
| Extension (A extends B) | N | M | 0 | 0 or small |
| Conflicting grammars | K | M-K | N-K | > 0 |

The `new_ambiguities` count is the key diagnostic: it reveals how many dispatch points become ambiguous when the grammars are merged. A zero count means the grammars compose cleanly.

---

## 4. Algebraic Properties

The lattice operations on `DecisionAction` satisfy the standard laws, which enables compositional reasoning about grammar operations:

### Commutativity

```text
A ⊔ B = B ⊔ A    (merge order doesn't matter)
A ⊓ B = B ⊓ A    (intersection is symmetric)
```

### Associativity

```text
(A ⊔ B) ⊔ C = A ⊔ (B ⊔ C)
```

This means merging three grammars can be done in any grouping order with the same result.

### Idempotence

```text
A ⊔ A = A    (merging a grammar with itself is a no-op)
A ⊓ A = A    (intersecting a grammar with itself gives itself)
```

PathMap detects this via `AlgebraicResult::Identity`, avoiding allocation.

### Absorption

```text
A ⊔ (A ⊓ B) = A    (merging A with what A and B share just gives A)
A ⊓ (A ⊔ B) = A    (intersecting A with the merger gives just A)
```

### Distributivity

```text
A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)
```

This is the key property that enables `psubtract` to be well-defined: in a distributive lattice, the relative complement is uniquely determined.

---

## 5. Practical Applications

### Grammar Extension Validation

When a language extension adds new rules to a base grammar:

```rust
let report = composition_trie_analysis(&base_tree, &extension_tree);
if report.new_ambiguities > 0 {
    emit_diagnostic(X06, "Extension introduces {n} dispatch ambiguities");
}
```

### Dead Rule Detection Confirmation

The pattern trie's dependency groups can be cross-referenced with composition analysis:

```text
If A ∖ B yields rule R, and R is in a dependency group with no seed terms,
then R is dead in the composed grammar.
```

### Diagnostic Output (X06)

The composition analysis feeds into the lint layer's X06 diagnostic, which reports:
- Number of shared rules between composed grammars
- Unique contributions of each grammar
- New ambiguities introduced by composition
- Specific dispatch points where conflicts occur

---

## 6. Complexity

All three lattice operations traverse both tries simultaneously:

| Operation | Time complexity | Space complexity |
|-----------|----------------|------------------|
| `A.join(&B)` | O(min(\|A\|, \|B\|)) | O(\|A\| + \|B\|) worst case |
| `A.meet(&B)` | O(min(\|A\|, \|B\|)) | O(min(\|A\|, \|B\|)) |
| `A.subtract(&B)` | O(min(\|A\|, \|B\|)) | O(\|A\|) |

where \|A\| and \|B\| are the number of trie nodes (not rules). Thanks to prefix sharing, \|A\| is typically much smaller than the number of rules.

---

## Key Source Files

| File | Lines | Role |
|------|-------|------|
| `prattail/src/decision_tree.rs` | 139-227 | `DecisionAction` Lattice/DistributiveLattice impls |
| `prattail/src/decision_tree.rs` | 2054-2104 | `composition_trie_analysis()` |
| External: PathMap crate | — | `join()`, `meet()`, `subtract()` trie operations |

---

**Next:** [Ascent Overview](../ascent-datalog/overview.md) — the Datalog engine that complements PathMap's structural indexing.
