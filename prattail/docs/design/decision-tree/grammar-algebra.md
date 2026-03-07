# PraTTaIL Decision Tree — Grammar Algebra

| Metadata | Value                                                                             |
|----------|-----------------------------------------------------------------------------------|
| Date     | 2026-03-06                                                                        |
| Updated  | 2026-03-06                                                                        |
| Source   | `prattail/src/decision_tree.rs` (L139-227, L1348-1401), `prattail/src/compose.rs` |

---

## Table of Contents

- [§1 Overview](#1-overview)
- [§2 Lattice Structure of DecisionAction](#2-lattice-structure-of-decisionaction)
- [§3 PathMap Meet — Common Sublanguage](#3-pathmap-meet--common-sublanguage)
- [§4 PathMap Subtract — Unique Rules](#4-pathmap-subtract--unique-rules)
- [§5 PathMap Join — Union with Ambiguity Detection](#5-pathmap-join--union-with-ambiguity-detection)
- [§6 composition_trie_analysis()](#6-composition_trie_analysis)
- [§7 Lattice Diagrams](#7-lattice-diagrams)
- [§8 Worked Example — Language Composition](#8-worked-example--language-composition)
- [§9 Diagnostic Output (X06)](#9-diagnostic-output-x06)
- [§10 Algebraic Properties](#10-algebraic-properties)

---

## §1 Overview

PathMap's lattice operations (`join`, `meet`, `subtract`) enable algebraic
analysis of grammar composition.  Given two grammars' decision trees, the
algebra answers three questions:

| Question                                        | Operation                       | Function                  |
|-------------------------------------------------|---------------------------------|---------------------------|
| What rules do both grammars share?              | `meet` (intersection)           | `tree_a.meet(tree_b)`     |
| What rules are unique to each grammar?          | `subtract` (difference)         | `tree_a.subtract(tree_b)` |
| What new ambiguities arise from combining them? | `join` (union) + ambiguity scan | `tree_a.join(tree_b)`     |

These operations are exposed through `composition_trie_analysis()`
(L1351-1392), which computes all three and returns a `CompositionTrieReport`.

The algebra operates on the **root segment** (segment 0) of each category's
decision tree.  Continuation segments are not composed — they are linked to
specific rules and are meaningful only in the context of their originating
grammar.

---

## §2 Lattice Structure of DecisionAction

`DecisionAction` implements the `Lattice` and `DistributiveLattice` traits
from PathMap's ring module.  These implementations define how values at the
same trie path are combined under each algebraic operation.

### §2.1 DecisionAction Variants

```
  DecisionAction
  ├── Commit { rule_label, category, weight }       — single deterministic rule
  ├── Ambiguous { candidates: Vec<AmbiguousCandidate> }  — multiple competing rules
  └── NonterminalBoundary { options: Vec<NTOption> }     — NT dispatch point
```

### §2.2 pjoin — Join (Union, Merge)

`pjoin` combines two actions at the same path.  The result is either the merged
action or an `AlgebraicResult` identity/none signal:

```
  pjoin(Commit(A), Commit(B))
      = Element(Ambiguous { candidates: [A, B] })

  pjoin(Ambiguous(cs), Commit(B))
      = Element(Ambiguous { candidates: cs ++ [B] })

  pjoin(Commit(A), Ambiguous(cs))
      = Element(Ambiguous { candidates: [A] ++ cs })

  pjoin(Ambiguous(cs₁), Ambiguous(cs₂))
      = Element(Ambiguous { candidates: cs₁ ++ cs₂ })

  pjoin(NonterminalBoundary, _)
      = Identity(1)     // preserve the boundary

  pjoin(_, NonterminalBoundary)
      = Identity(2)     // preserve the boundary
```

**Semantics:** Joining two grammars at a path creates an ambiguity if both
grammars have a rule at that path.  The `Ambiguous` variant records all
competing candidates for diagnostic reporting.

### §2.3 pmeet — Meet (Intersection)

`pmeet` retains only rules present in both actions:

```
  pmeet(A, B):
      labels_A ← A.rule_labels()
      labels_B ← B.rule_labels()
      common ← labels_A ∩ labels_B

      if common = ∅:
          return None       // no shared rules at this path

      candidates ← A.all_candidates().filter(c → c.label ∈ common)
      if |candidates| = 1:
          return Element(Commit(candidates[0]))
      else:
          return Element(Ambiguous { candidates })
```

**Semantics:** The meet computes the common sublanguage — rules that exist in
both grammars at the same trie path.  A rule is "shared" if and only if both
grammars assign it to the same byte path.

### §2.4 psubtract — Subtract (Difference)

`psubtract` removes rules present in the other action:

```
  psubtract(A, B):
      labels_B ← B.rule_labels()
      remaining ← A.all_candidates().filter(c → c.label ∉ labels_B)

      if remaining = ∅:
          return None       // all rules were in B
      if |remaining| = 1:
          return Element(Commit(remaining[0]))
      else:
          return Element(Ambiguous { remaining })
```

**Semantics:** The subtraction isolates rules unique to grammar A that are not
in grammar B.  This is the complement of the meet with respect to A.

---

## §3 PathMap Meet — Common Sublanguage

### §3.1 Definition

For two PathMaps P_A and P_B over the same key space, the meet is:

```
  P_A ⊓ P_B = { (path, pmeet(v_A, v_B)) | path ∈ dom(P_A) ∩ dom(P_B)
                                            and pmeet(v_A, v_B) ≠ None }
```

Only paths present in **both** tries contribute to the result.  At each shared
path, `pmeet` retains only the rules common to both values.

### §3.2 Usage

```rust
let common = tree_a.segments[0].meet(&tree_b.segments[0]);
let common_count = common.val_count();
```

### §3.3 Interpretation

| Result | Meaning |
|--------|---------|
| `common_count = 0` | Grammars have no shared rules (completely disjoint) |
| `common_count > 0` | Grammars share `common_count` rules at the same paths |

Shared rules indicate structural overlap — the same rule appears in both
grammars with the same terminal prefix encoding.  This is useful for:

- Detecting grammar inheritance (B extends A → meet contains A's rules)
- Identifying stable core rules during grammar evolution
- Validating that a grammar refactoring preserves existing rules

---

## §4 PathMap Subtract — Unique Rules

### §4.1 Definition

```
  P_A ⊖ P_B = { (path, psubtract(v_A, v_B)) | path ∈ dom(P_A)
                                                 and psubtract(v_A, v_B) ≠ None }
```

For paths only in P_A (not in P_B), the value is retained unchanged (the
subtraction of a missing value is identity).  For paths in both, only the rules
unique to A remain.

### §4.2 Usage

```rust
let unique_a = tree_a.segments[0].subtract(&tree_b.segments[0]);
let unique_b = tree_b.segments[0].subtract(&tree_a.segments[0]);
let unique_a_count = unique_a.val_count();
let unique_b_count = unique_b.val_count();
```

### §4.3 Interpretation

| Result             | Meaning                                     |
|--------------------|---------------------------------------------|
| `unique_a_count`   | Rules in A not present in B                 |
| `unique_b_count`   | Rules in B not present in A                 |
| Both = 0           | Grammars are identical (at the trie level)  |
| One = 0, other > 0 | One grammar is a strict subset of the other |

### §4.4 Identity Check

The meet and subtract satisfy:

```
  |P_A| = |P_A ⊓ P_B| + |P_A ⊖ P_B|
```

Every rule in A is either shared with B (in the meet) or unique to A (in the
subtraction).

---

## §5 PathMap Join — Union with Ambiguity Detection

### §5.1 Definition

```
  P_A ⊔ P_B = { (path, v) | path ∈ dom(P_A) ∪ dom(P_B) }
      where v = pjoin(P_A[path], P_B[path])  if path ∈ dom(P_A) ∩ dom(P_B)
            v = P_A[path]                     if path ∈ dom(P_A) \ dom(P_B)
            v = P_B[path]                     if path ∈ dom(P_B) \ dom(P_A)
```

### §5.2 New Ambiguity Detection

The critical use of join is detecting **new ambiguities** that arise from
combining two grammars.  After computing the join, the composition analysis
scans for `Ambiguous` nodes:

```rust
// From composition_trie_analysis (L1375-1384):
let merged = tree_a.segments[0].join(&tree_b.segments[0]);
let mut new_ambiguities = 0;
for (_path, action) in merged.iter() {
    if let DecisionAction::Ambiguous { candidates } = action {
        if candidates.len() > 1 {
            new_ambiguities += 1;
        }
    }
}
```

### §5.3 Interpretation

| `new_ambiguities` | Meaning                                                        |
|-------------------|----------------------------------------------------------------|
| 0                 | Safe composition — no new prefix conflicts                     |
| > 0               | Composition introduces N new ambiguities requiring NFA try-all |

New ambiguities arise when:

1. Grammar A has rule R_A at path P, and grammar B has rule R_B at the same
   path P.  `pjoin` creates `Ambiguous { [R_A, R_B] }`.

2. Grammar A has an `Ambiguous` node at path P (pre-existing ambiguity), and
   grammar B adds another candidate.  The candidate count increases.

Pre-existing ambiguities within a single grammar (before composition) are not
counted as "new" — only ambiguities that result from the join of two distinct
grammars are new.

---

## §6 composition_trie_analysis()

### §6.1 Function Signature

```rust
pub fn composition_trie_analysis(
    tree_a: &CategoryDecisionTree,
    tree_b: &CategoryDecisionTree,
) -> CompositionTrieReport
```

### §6.2 CompositionTrieReport

```rust
pub struct CompositionTrieReport {
    pub common_rules: usize,      // |meet|  — rules shared by both
    pub unique_a: usize,          // |A ⊖ B| — rules only in A
    pub unique_b: usize,          // |B ⊖ A| — rules only in B
    pub new_ambiguities: usize,   // ambiguous nodes in join not in either source
}
```

### §6.3 Algorithm

```
fn composition_trie_analysis(tree_a, tree_b):
    if tree_a.segments empty or tree_b.segments empty:
        return { 0, 0, 0, 0 }

    common      ← tree_a.segments[0].meet(tree_b.segments[0])
    unique_a    ← tree_a.segments[0].subtract(tree_b.segments[0])
    unique_b    ← tree_b.segments[0].subtract(tree_a.segments[0])
    merged      ← tree_a.segments[0].join(tree_b.segments[0])

    common_count   ← common.val_count()
    unique_a_count ← unique_a.val_count()
    unique_b_count ← unique_b.val_count()

    new_ambiguities ← 0
    for (path, action) in merged.iter():
        if action is Ambiguous with |candidates| > 1:
            new_ambiguities += 1

    return CompositionTrieReport {
        common_rules: common_count,
        unique_a: unique_a_count,
        unique_b: unique_b_count,
        new_ambiguities,
    }
```

### §6.4 Complexity

Each PathMap operation (meet, subtract, join) traverses both tries
simultaneously, visiting each path at most once.  For tries with N_A and N_B
entries:

```
  Time:  O(N_A + N_B) per operation × 4 operations = O(N_A + N_B)
  Space: O(N_A + N_B) for the result tries
```

---

## §7 Lattice Diagrams

### §7.1 DecisionAction Lattice

The `DecisionAction` lattice is ordered by specificity:

```
                    ┌──────────────────────┐
                    │ Ambiguous(all rules) │ ← top (least specific)
                    └──────────┬───────────┘
                               │
                   ┌───────────┼───────────┐
                   │           │           │
            Ambiguous(A,B) Ambiguous(B,C) Ambiguous(A,C)
                   │           │           │
                   └───────────┼───────────┘
                               │
                   ┌───────────┼───────────┐
                   │           │           │
              Commit(A)   Commit(B)   Commit(C) ← atoms
                   │           │           │
                   └───────────┼───────────┘
                               │
                          ┌────┴────┐
                          │  None   │ ← bottom (no rule)
                          └─────────┘
```

Operations:

```
  pjoin(Commit(A), Commit(B))  = Ambiguous(A,B)     ↑ toward top
  pmeet(Commit(A), Commit(B))  = None                ↓ toward bottom
  pmeet(Ambiguous(A,B), Commit(A)) = Commit(A)       ↓ toward bottom
  psubtract(Ambiguous(A,B), Commit(B)) = Commit(A)   ↓ toward bottom
```

### §7.2 PathMap Lattice Operations

For two PathMaps representing grammars:

```
  Grammar A trie:                Grammar B trie:
  ┌─────────────────┐            ┌─────────────────┐
  │ [0x03] → R₁     │            │ [0x03] → R₃     │
  │ [0x05] → R₂     │            │ [0x07] → R₄     │
  └─────────────────┘            └─────────────────┘

  Meet (A ⊓ B):                  Join (A ⊔ B):
  ┌─────────────────┐            ┌───────────────────────────┐
  │ [0x03] → pmeet  │            │ [0x03] → Ambiguous(R₁,R₃) │
  │         (R₁,R₃) │            │ [0x05] → R₂               │
  └─────────────────┘            │ [0x07] → R₄               │
                                 └───────────────────────────┘

  Subtract (A ⊖ B):             Subtract (B ⊖ A):
  ┌─────────────────┐            ┌─────────────────┐
  │ [0x05] → R₂     │            │ [0x07] → R₄     │
  └─────────────────┘            └─────────────────┘
```

For the meet at path `[0x03]`:

- If `R₁.label = R₃.label` → meet yields `Commit(R₁)` (same rule in both)
- If `R₁.label ≠ R₃.label` → meet yields `None` (different rules; no shared rule at this path)

For the join at path `[0x03]`:

- If `R₁.label = R₃.label` → join yields `Ambiguous([R₁, R₃])` (technically same rule, counted as ambiguity by the scan)
- If `R₁.label ≠ R₃.label` → join yields `Ambiguous([R₁, R₃])` (genuine new ambiguity)

### §7.3 Venn Diagram of Rule Sets

```
  ┌───────────────────────────────────────────────────────┐
  │                       A ⊔ B                           │
  │  ┌──────────────┐  ┌─────────┐  ┌──────────────┐      │
  │  │    A ⊖ B     │  │  A ⊓ B  │  │    B ⊖ A     │      │
  │  │  (unique A)  │  │ (common)│  │  (unique B)  │      │
  │  │              │  │         │  │              │      │
  │  │  e.g. R₂     │  │ R₁=R₃?  │  │  e.g. R₄     │      │
  │  └──────────────┘  └─────────┘  └──────────────┘      │
  │                                                       │
  │  new_ambiguities = paths where both A and B have      │
  │                    different rules                    │
  └───────────────────────────────────────────────────────┘
```

---

## §8 Worked Example — Language Composition

### §8.1 Grammar Definitions

**Grammar A (Arithmetic):**

```
  Category: Expr
    IntLit:     <IntegerLiteral>          (native type — not in RD trie)
    Neg:        - <Expr>                  (unary prefix — not in RD trie)
    IfExpr:     if <Expr> then <Expr>
    LetExpr:    let x = <Expr>
```

**Grammar B (Boolean Extension):**

```
  Category: Expr
    BoolLit:    true | false              (native type — not in RD trie)
    IfExpr:     if <Expr> then <Expr>     (same rule as A)
    WhileExpr:  while <Expr> do <Expr>
```

### §8.2 Token ID Assignments

| Variant   | Byte ID |
|-----------|---------|
| `Eq`      | 0x00    |
| `KwDo`    | 0x01    |
| `KwIf`    | 0x02    |
| `KwLet`   | 0x03    |
| `KwThen`  | 0x04    |
| `KwWhile` | 0x05    |

### §8.3 Trie Contents

**Grammar A — Expr root segment:**

```
  [0x02]            → Commit("IfExpr",  category="Expr", weight=0.0)
  [0x03, 0x80, 0x00] → Commit("LetExpr", category="Expr", weight=0.0)
```

**Grammar B — Expr root segment:**

```
  [0x02]     → Commit("IfExpr",    category="Expr", weight=0.0)
  [0x05]     → Commit("WhileExpr", category="Expr", weight=0.0)
```

### §8.4 Composition Analysis

```
  meet(A, B):
    Path [0x02]: pmeet(Commit("IfExpr"), Commit("IfExpr"))
      labels_A = {"IfExpr"}, labels_B = {"IfExpr"}
      common = {"IfExpr"}
      → Element(Commit("IfExpr"))

    Path [0x03, 0x80, 0x00]: only in A → not in meet
    Path [0x05]: only in B → not in meet

    Result: { [0x02] → Commit("IfExpr") }
    common_count = 1

  subtract(A, B):
    Path [0x02]: psubtract(Commit("IfExpr"), Commit("IfExpr"))
      other_labels = {"IfExpr"}
      remaining = [] (IfExpr removed)
      → None

    Path [0x03, 0x80, 0x00]: not in B → retained as-is
      → Commit("LetExpr")

    Result: { [0x03, 0x80, 0x00] → Commit("LetExpr") }
    unique_a = 1

  subtract(B, A):
    Path [0x02]: psubtract(Commit("IfExpr"), Commit("IfExpr"))
      → None (removed)

    Path [0x05]: not in A → retained as-is
      → Commit("WhileExpr")

    Result: { [0x05] → Commit("WhileExpr") }
    unique_b = 1

  join(A, B):
    Path [0x02]: pjoin(Commit("IfExpr"), Commit("IfExpr"))
      → Ambiguous { candidates: [IfExpr(A), IfExpr(B)] }

    Path [0x03, 0x80, 0x00]: only in A
      → Commit("LetExpr")

    Path [0x05]: only in B
      → Commit("WhileExpr")

    Ambiguity scan: [0x02] has Ambiguous with 2 candidates → count 1
    new_ambiguities = 1
```

### §8.5 CompositionTrieReport

```
  CompositionTrieReport {
      common_rules: 1,       // IfExpr shared at path [0x02]
      unique_a: 1,           // LetExpr only in A
      unique_b: 1,           // WhileExpr only in B
      new_ambiguities: 1,    // IfExpr × IfExpr at [0x02]
  }
```

Note: The `new_ambiguities` count of 1 is technically a false positive — both
grammars have the **same** rule `IfExpr` at path `[0x02]`, so there is no
genuine conflict.  The current implementation counts all `Ambiguous` nodes in
the join, including self-joins of identical rules.  A refinement would check
whether all candidates in an `Ambiguous` node share the same `rule_label` and
exclude those from the count.

### §8.6 Composed Trie

After composition, the merged Expr trie contains:

```
  ┌─────────────────────────────────────────────────────────┐
  │  Root segment (composed Expr):                          │
  │                                                         │
  │  [0x02]             → Ambiguous(IfExpr, IfExpr)         │
  │  [0x03, 0x80, 0x00] → Commit(LetExpr)                   │
  │  [0x05]             → Commit(WhileExpr)                 │
  │                                                         │
  │  After deduplication (if implemented):                  │
  │  [0x02]             → Commit(IfExpr)                    │
  │  [0x03, 0x80, 0x00] → Commit(LetExpr)                   │
  │  [0x05]             → Commit(WhileExpr)                 │
  └─────────────────────────────────────────────────────────┘
```

---

## §9 Diagnostic Output (X06)

### §9.1 X06 — Composition Verification Violation

When grammar composition is performed via `compose_languages()` in
`compose.rs`, the composition verification test (CVT) checks several structural
properties of the merged result.  Violations are reported as X06 diagnostics.

**Diagnostic format:**

```
  warning[X06]: composition verification [<property>]: <violation>
    hint: review the composed grammar for property violations
```

**Properties checked:**

| Property               | Description                                              |
|------------------------|----------------------------------------------------------|
| `NoSpuriousActions`    | Merged WFST contains no actions absent from both A and B |
| `WeightPreservation`   | Action weights are preserved within tolerance            |
| `StateReachability`    | All states in the merged WFST are reachable              |
| `CategoryCompleteness` | All categories from A and B are present in the result    |

**Example output:**

```
  warning[X06]: composition verification [NoSpuriousActions]:
    action "PhantomRule" in merged WFST is not present in either source grammar
    hint: review the composed grammar for property violations

  warning[X06]: composition verification [WeightPreservation]:
    action "IfExpr" has weight 0.5 in A but 0.8 in merged
    hint: review the composed grammar for property violations
```

### §9.2 D01 — Precision Ambiguity (from Decision Tree)

When `composition_trie_analysis()` reports `new_ambiguities > 0`, the
precision ambiguity analysis layer (D01) provides detailed path-level
information:

```
  note[D01]: ambiguity at [KwIf] between IfExpr(A) and IfExpr(B)
    hint: adding a distinguishing terminal before the divergence point
          would resolve the ambiguity between IfExpr(A) and IfExpr(B)
```

### §9.3 D05 — Complexity Metrics (Post-Composition)

After composition, the D05 layer reports the merged tree's statistics:

```
  note[D05]: decision tree: 3 states (2 deterministic, 1 ambiguous),
    max depth 3, min lookahead 3, 0 NT boundaries, 0 shared-prefix savings,
    2/3 rules deterministic
```

---

## §10 Algebraic Properties

### §10.1 Join is Commutative

```
  P_A ⊔ P_B = P_B ⊔ P_A
```

`pjoin(A, B)` produces the same candidate set as `pjoin(B, A)` (order of
candidates may differ, but the set is identical).

### §10.2 Meet is Commutative

```
  P_A ⊓ P_B = P_B ⊓ P_A
```

`pmeet(A, B)` and `pmeet(B, A)` retain the same common labels.

### §10.3 Subtract is Not Commutative

```
  P_A ⊖ P_B ≠ P_B ⊖ P_A  (in general)
```

This is expected: the rules unique to A differ from those unique to B.

### §10.4 Decomposition Identity

```
  |P_A| = |P_A ⊓ P_B| + |P_A ⊖ P_B|
  |P_B| = |P_A ⊓ P_B| + |P_B ⊖ P_A|
```

Every entry in a trie is either common (in the meet) or unique (in the
subtraction).

### §10.5 Join Cardinality

```
  |P_A ⊔ P_B| = |P_A ⊖ P_B| + |P_B ⊖ P_A| + |P_A ⊓ P_B|
               = |P_A| + |P_B| − |P_A ⊓ P_B|
```

This is the inclusion-exclusion principle for trie path sets.  Note that the
**value** at shared paths in the join is the `pjoin` merge (potentially
`Ambiguous`), not a simple copy.

### §10.6 Distributivity

`DecisionAction` implements `DistributiveLattice`, which provides `psubtract`
as a derived operation satisfying:

```
  pjoin(A, psubtract(B, A)) = pjoin(A, B)
```

This means: joining A with "B minus A" gives the same result as joining A with
B.  The unique rules from B, when joined with A, reconstruct the full union.

### §10.7 Monotonicity of Ambiguity

```
  new_ambiguities(P_A ⊔ P_B) ≥ 0
  new_ambiguities(P_A ⊔ P_B) = 0  ⟺  dom(P_A) ∩ dom(P_B) maps to identical rules
```

Composition can only **add** ambiguity, never remove it.  If two grammars have
disjoint path domains, their join introduces zero new ambiguities.
