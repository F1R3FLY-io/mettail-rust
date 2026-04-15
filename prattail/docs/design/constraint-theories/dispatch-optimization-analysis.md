# Dispatch Optimization Analysis

**Companion to:** [Why Automata Instead of Solvers](why-automata-instead-of-solvers.md)
**See also:** [Symbolic Automata Research Analysis](symbolic-automata-research-analysis.md),
[Heyting Algebra Extensions](heyting-algebra-extensions.md)
**Status:** RESEARCH ANALYSIS -- §2 describes the implemented baseline;
all other sections describe proposals that are not yet implemented.

---

This document explores advanced indexing structures for optimizing the
dispatch of messages to guarded receives in MeTTaIL's predicated types
framework.  The main document ([Why Automata Instead of Solvers](why-automata-instead-of-solvers.md))
describes the compile-time SFA analysis pipeline (§2) and the three-layer
runtime dispatch architecture (§2.6).  This document focuses on **Layer 2**
(guard evaluation) and proposes domain-specific indexing structures that
could reduce dispatch cost from linear in the number of guards to
logarithmic or constant.

---

## 1. Introduction and Motivation

When a message `@(q)` arrives on a channel with `m` guarded receives, the
runtime must determine which guards are satisfied.  The **dispatch problem**
is: given guards `φ₁, …, φₘ` and a value `v`, find all `i` such that
`v ∈ ⟦φᵢ⟧`.

The main document's three-layer runtime architecture (§2.6) handles this as:

1. **Layer 1 (Structural dispatch):** token-based decision tree selects
   the category/rule.  Cost: `O(k)` prefix lookup.
2. **Layer 2 (Guard evaluation):** generated code evaluates the selected
   guard.  Cost: depends on guard type and number of candidates.
3. **Layer 3 (Behavioral predicates):** Ascent fixpoint relation lookup.
   Cost: `O(1)` per predicate.

This document focuses on Layer 2.  When multiple guards compete for the
same value, the naive approach tests each guard individually — `O(m)` for
`m` guards.  The **indexing question** is: can we precompute a data
structure that answers "which guards match `v`?" in `O(log m)` or `O(1)`?

The following abbreviations are used throughout; terms already defined in
the main document are cross-referenced rather than re-defined:

- **BSP** — Binary Space Partition (a tree that recursively divides space
  by hyperplanes)
- **vEB** — van Emde Boas tree (an integer data structure with
  `O(log log U)` operations over universe `[0, U)`)
- **WAM** — Warren Abstract Machine (the standard Prolog execution model)
- **JIT** — Just-In-Time (building indexes on demand at runtime)

> **Terminology from the main document:** minterm, SFA, SFT, `BooleanAlgebra`,
> `ProductAlgebra`, T1–T4, PathMap, WFST, Ascent — defined in
> [Why Automata Instead of Solvers](why-automata-instead-of-solvers.md) §1.

---

## 2. Minterm-Based Dispatch (Implemented Baseline)

> **Status:** This section describes the **currently implemented** approach.

**Minterms** (defined in the main document §2.4) partition the domain into
regions where every guard behaves identically.  A minterm for predicates
`Φ = {φ₁, …, φₙ}` is a maximal satisfiable conjunction:

    m = ψ₁ ∧ ψ₂ ∧ ⋯ ∧ ψₙ     where each ψᵢ ∈ {φᵢ, ¬φᵢ}

Within a single minterm, the set of matching guards is constant — every
value in the region satisfies exactly the same guards.

**Construction.** The SFA pipeline (main document §2.5, stages 3-5) computes
minterms at compile time:

1. Collect all guard predicates `Φ` from a channel's receives
2. Enumerate all `2ⁿ` candidate conjunctions
3. Test each for satisfiability via `SAT` (prune unsatisfiable ones)
4. For each satisfiable minterm, record the set of matching guards

**Runtime dispatch.** Given a value `v`, identify which minterm region `v`
falls into, then look up the pre-recorded guard set.  The identification
step is the bottleneck: in the worst case, each minterm boundary must be
tested, costing `O(m)` comparisons for `m` minterms.

**Example.** Three guards on an integer channel (from main document §2.4):

```
  Guard A: x ∈ [0, 50)       Guard B: x ∈ [30, 100)      Guard C: x ∈ [80, ∞)

  Minterms:  [0,30)→{A}   [30,50)→{A,B}   [50,80)→{B}   [80,100)→{B,C}   [100,∞)→{C}
```

At runtime, the generated code tests: `x < 30?  x < 50?  x < 80?  x < 100?`
— a linear scan over minterm boundaries.

**Complexity:**

| Phase | Cost | When |
|-------|------|------|
| Construction | `O(2ⁿ · T_SAT)` | Compile time |
| Runtime dispatch | `O(m)` boundary tests | Per message |

**Strengths:** Correct and complete for any `BooleanAlgebra` backend.
Universal — works for integer, character, Presburger, and composed guards.

**Limitation:** The `O(m)` runtime cost is linear in the number of minterm
boundaries.  For channels with many guards (m > 20), this linear scan
dominates dispatch time.  The subsequent sections propose indexing
structures that reduce this to `O(log m)` or `O(1)` for specific guard
domains.

---

## 3. Numeric Guard Dispatch

### 3.1 Single-Variable: Segment Trees and Interval Trees

For guards constraining a single integer variable — `x ≥ a ∧ x < b` — the
minterm boundaries form a sorted sequence of interval endpoints on the
number line.  The dispatch question becomes a **point stabbing query**: given
a point `x`, which intervals contain it?

A **segment tree** (de Berg et al., 2008) answers this in `O(log m)` after
`O(m log m)` construction:

**Intuition.** A segment tree is a balanced binary tree over the sorted
interval endpoints.  Each internal node represents a range of the number
line.  Each guard's interval is "pushed down" to the minimal set of tree
nodes that exactly cover it.  A point query descends from root to leaf,
collecting the guards stored at each node along the path — exactly
`O(log m)` nodes.

```
╔══════════════════════════════════════════════════════════════════════════╗
║  SEGMENT_TREE_DISPATCH(endpoints: [e₁, …, e₂ₘ], guards: [φ₁, …, φₘ])   ║
║                                                                          ║
║  Build a segment tree for point-stabbing queries over guard intervals.   ║
║                                                                          ║
║  ── Construction (compile time, O(m log m)) ───────────────────────────  ║
║                                                                          ║
║  1. Sort all interval endpoints: e₁ < e₂ < ⋯ < e₂ₘ                      ║
║  2. Build a balanced binary tree over the 2m+1 elementary intervals:     ║
║     (-∞, e₁), [e₁, e₁], (e₁, e₂), [e₂, e₂], …, (e₂ₘ, +∞)             ║
║  3. For each guard φᵢ with interval [aᵢ, bᵢ):                           ║
║     Push φᵢ into the minimal set of tree nodes covering [aᵢ, bᵢ)        ║
║                                                                          ║
║  ── Query (runtime, O(log m + k)) ─────────────────────────────────────  ║
║                                                                          ║
║  Given value x:                                                          ║
║  1. Descend from root, choosing left/right based on x vs. node midpoint  ║
║  2. At each node, collect all guards stored there → these match x        ║
║  3. Return union of collected guards                                     ║
║                                                                          ║
║  Total: O(log m) nodes visited + O(k) guards collected (k = output)     ║
╚══════════════════════════════════════════════════════════════════════════╝
```

An **interval tree** (Edelsbrunner, 1980) is an alternative with `O(n + k)`
query time (where `k` is the number of matching intervals).  For the
dispatch use case where we want *all* matching guards, the interval tree
may have better constants than the segment tree.

For bounded integer universes `[0, U)`, a **van Emde Boas (vEB) tree**
achieves `O(log log U)` predecessor/successor queries — faster than
balanced BSTs when `U` is known at compile time (e.g., `U = 2¹⁶ = 65536`
for 16-bit guard predicates).

### 3.2 Multi-Variable: BSP Trees and Hyperplane Arrangements

For guards constraining multiple integer variables — `Σ aᵢ · xᵢ ≤ b` —
the constraint regions are **halfspaces** in `ℝᵏ`.  The dispatch question
becomes: given a point `(x₁, …, xₖ)`, which halfspaces contain it?

A **Binary Space Partition (BSP) tree** recursively divides space by
hyperplanes.  Each internal node stores one hyperplane (one guard
constraint); the left child contains the "satisfies" region and the right
child contains the "violates" region.  Leaves identify the complete guard
set for their cell.

**Intuition.** A BSP tree is the geometric analog of a decision tree: each
node asks "which side of this hyperplane is the point on?" and branches
accordingly.  After `O(log m)` decisions, the leaf identifies all matching
guards.

The collection of all guard hyperplanes partitions `ℝᵏ` into an
**arrangement** — a cellular decomposition where each cell maps to a fixed
set of matching guards.  This is exactly the geometric version of minterm
partitioning.  A **point location** query in the arrangement identifies the
cell containing a given point.

```
  Three linear guards in ℝ²:

  Guard A: x + y ≤ 100     Guard B: x ≥ 10         Guard C: y ≥ 20

                y
                ↑
           100  ╲
                 ╲  A ∧ ¬B ∧ C
                  ╲
                   ╲  A ∧ B ∧ C        BSP node: x + y ≤ 100?
           20 ┈┈┈┈┈╲┈┈┈┈┈┈┈             ╱           ╲
                    ╲  A ∧ B ∧ ¬C      yes             no
                     ╲               BSP: x ≥ 10?    BSP: x ≥ 10?
                ──────╲──────▶ x      ╱    ╲          ╱    ╲
               10                  ...    ...      ...    ...
```

**Complexity comparison:**

| Structure | Build | Query | Space | Dimensions |
|-----------|-------|-------|-------|------------|
| Linear scan (current) | `O(m)` | `O(m)` | `O(m)` | Any `k` |
| Segment tree | `O(m log m)` | `O(log m + k)` | `O(m log m)` | `k = 1` only |
| Interval tree | `O(m log m)` | `O(log m + k)` | `O(m)` | `k = 1` only |
| vEB tree | `O(m)` | `O(log log U)` | `O(U)` | `k = 1`, bounded `U` |
| BSP tree | `O(m²)` | `O(log m)` | `O(m²)` | `k = 2` |
| k-d tree | `O(m log m)` | `O(m^(1−1/k) + output)` | `O(m)` | Any `k` |
| R-tree | `O(m log m)` | `O(log m + output)` | `O(m)` | Any `k` |

---

## 4. String/Sequence Guard Dispatch

### 4.1 Exact String Guards

For guards testing exact string equality — `name = "cowboy"` — a
**hash table** provides `O(1)` expected-time dispatch: hash the input string
and look up the matching guard.  For `m` exact-match guards, construction
is `O(m)` and each query is `O(|s|)` (hashing the input string of length
`|s|`).

A **trie** over the guard strings provides `O(|s|)` worst-case dispatch
with shared prefix compression.  When multiple guards share prefixes
(e.g., `"cowboy"`, `"cowgirl"`, `"cowpoke"`), the trie branches only at
the divergence points:

```
  Root ──c──▶ ──o──▶ ──w──▶ ┬──b──▶ ──o──▶ ──y──▶ ● (Guard A: "cowboy")
                             ├──g──▶ ──i──▶ ──r──▶ ──l──▶ ● (Guard B: "cowgirl")
                             └──p──▶ ──o──▶ ──k──▶ ──e──▶ ● (Guard C: "cowpoke")
```

### 4.2 Prefix and Suffix Guards

For guards testing string prefixes — `prefix(name, "cow")` — the same trie
structure works: traverse the trie for the prefix and accept at any internal
node that is marked as a prefix-match accepting state.

For suffix guards — `suffix(name, "boy")` — build a **reversed-string trie**
over the reversed suffixes.  Query time: `O(|suffix|)`.

### 4.3 String Decomposition: Composed Trie Automata

For guards constraining a decomposition — `x + y = "cowboy"` — the guard
asks whether the input can be split into `(x, y)` such that `x · y` equals
the target.  This is not a simple membership test; it's a search over
split points.

**Composed trie automata** solve this by building a tensor product of a
prefix trie and a suffix trie:

```
╔══════════════════════════════════════════════════════════════════════════╗
║  COMPOSED_TRIE_DISPATCH(target: string, x: string, y: string) → bool    ║
║                                                                          ║
║  Determine whether x · y = target using composed trie automata.          ║
║                                                                          ║
║  ── Construction (compile time) ───────────────────────────────────────  ║
║                                                                          ║
║  T_prefix ← trie accepting all prefixes of target                        ║
║             Each accepting state qᵢ records split position i             ║
║  T_suffix ← trie indexed by split position                               ║
║             State qᵢ accepts suffix target[i..]                          ║
║                                                                          ║
║  ── Query (runtime, O(|x| + |y|)) ────────────────────────────────────  ║
║                                                                          ║
║  1. Run x through T_prefix → reach state qᵢ (or reject)                 ║
║  2. Run y through T_suffix starting from qᵢ → accept iff y matches      ║
║                                                                          ║
║  The composition T_prefix ⊗ T_suffix synchronizes at the split point:   ║
║  state (qᵢ, qⱼ) is accepting iff i = j.                                 ║
╚══════════════════════════════════════════════════════════════════════════╝
```

For multiple target strings, the prefix tries merge into a single shared
trie (analogous to Aho-Corasick).  The query cost remains `O(|x| + |y|)`,
independent of the number of guards.

This generalizes to k-way decomposition (`x · y · z = target`) via k-fold
trie composition, and to non-string domains: any decomposition guard
`f(x₁, …, xₖ) = target` where `f` is associative can use the same
structure.

### 4.4 Regex Guards and Multi-Pattern Matching

For guards testing regular expression membership — `matches(name, "cow.*")`
— the SFA framework (main document §3) already provides the correct
approach for individual guards.  The optimization opportunity is
**multi-pattern matching**: given `m` regex guards, match the input against
all `m` simultaneously.

The **Aho-Corasick automaton** (Aho & Corasick, 1975) handles multiple
literal patterns in `O(|s| + output)` total time (not `O(m · |s|)`).  For
general regex patterns, the **SFA product construction** computes the product
of all `m` guard SFAs; a single traversal of the input against the product
identifies all matching guards.

For industrial-scale multi-pattern matching (thousands of patterns), the
**Hyperscan** architecture (Wang et al., 2019) decomposes each regex into
literal triggers (fast SIMD-accelerated matching via shift-mask) plus small
NFA suffixes (checked only when triggers fire).  The decomposition principle
applies to guard dispatch: extract the most discriminating literal fragment
from each guard as a fast pre-filter, then fall back to full SFA evaluation
only for candidates that pass the literal filter.

A recent advance is **symbolic Brzozowski derivatives** (RE#; Varatalu,
Veanes & Ernits, 2025): the **derivative** of a regex `R` with respect to
a character `a` is a new regex `δₐ(R)` matching the suffixes of `L(R)` that
start with `a`.  Lifted to SFA predicates, symbolic derivatives compute
successor states lazily without materializing the full DFA — naturally
supporting intersection, complement, and multi-pattern matching.  This
connects to the symbolic transition terms from Veanes et al. (2023)
discussed in the [research analysis](symbolic-automata-research-analysis.md)
§4.2.

### 4.5 Word Equations

The most general string constraint is a **word equation**: `x · y · z = w`
where the variables and the target may all be partially unknown.  Word
equations are decidable (Makanin, 1977) but the general decision procedure
has high complexity (PSPACE; Plandowski, 2004).

For guard predicates in practice, word equations are rare and the target
string is usually known at compile time, reducing the problem to
enumeration of split points (§4.3).

---

## 5. Structural Guard Dispatch (Algebraic and Abstract Data Types)

Two kinds of data types require structural dispatch:

- **Algebraic data types** are defined by constructors (`Option = None | Some(T)`,
  `List = Nil | Cons(T, List)`).  The compiler can see the internal structure
  and pattern-match on it.  §§5.1–5.2 address this case.
- **Abstract data types** are defined by an interface (`Stack` with `push`,
  `pop`, `isEmpty`).  The compiler can only observe behavior through method
  calls, not inspect internals.  §5.2 (nested indexing on method results)
  and the Heyting algebra framework
  ([Heyting Algebra Extensions](heyting-algebra-extensions.md) §6) address
  this case — observable properties form a Heyting algebra, and compile-time
  analysis uses the `BooleanApproximation` bridge for conservative dispatch.

### 5.1 Constructor Matching: Discrimination Trees

For guards matching **algebraic** data type constructors —
`@{App(f, Var(x))}` — the dispatch question is: given a ground term, which
guard patterns unify with it?

A **discrimination tree** (Sekar, Ramakrishnan & Voronkov, 2001) is a trie
where each level branches on a position in the term:

1. First level: branch on the root constructor (e.g., `App` vs. `Var` vs. `Const`)
2. Second level: branch on the first child's constructor
3. And so on, recursively into subterms

**Intuition.** A discrimination tree is like a decision tree specialized for
term structure: each node asks "what constructor is at this position?" and
branches on the answer.  Variables in patterns match any constructor — they
correspond to "wildcard" edges that follow all branches.

```
  Patterns:
    P₁: App(f, Var(x))      P₂: App(f, Const(a))      P₃: Var(y)

  Discrimination tree:
    Root: constructor at position ε?
      ├── App → constructor at position 2?
      │         ├── Var → {P₁}
      │         ├── Const → {P₂}
      │         └── * (other) → ∅
      ├── Var → {P₃}
      └── * (other) → ∅
```

Query time: `O(|t|)` where `|t|` is the term size — the tree visits each
position once.

A **substitution tree** (Graf, 1995) compresses discrimination trees by
factoring out common substitutions.  When many patterns share substructure
(e.g., all match `App(_, _)` but differ in the second argument), the
substitution tree stores the shared prefix once and attaches differential
substitutions at branch points.

MeTTaIL's PathMap byte trie (main document §2.6) is already a form of
discrimination tree — it branches on the flattened byte representation of
terms.  The primary optimization opportunity is substitution tree
compression for pattern sets with heavy sharing.

### 5.2 Deep Field Access: Nested Indexing

For guards accessing nested fields — `person.age ≥ 18` — the dispatch
decomposes into two steps: navigate to the field, then apply a
domain-specific index on the field's value.

A **nested index** addresses this by building a tree of indexes:

```
  Outer index (field path trie):
    "person" → "age"   → Inner index: segment tree over [0, ∞)
    "person" → "name"  → Inner index: hash table / trie
    "order"  → "total" → Inner index: segment tree over [0, ∞)
```

The outer index is a PathMap-compatible byte trie keyed by field access
paths.  Each leaf is a domain-specific index for that field's type:
`IntervalAlgebra` segment tree for numeric fields, hash/trie for string
fields, discrimination tree for ADT fields.

### 5.3 Cross-Field Constraints

For guards relating multiple fields — `tree.left > tree.right` — the
constraint spans two positions in the structure.  This is fundamentally
harder than single-field indexing because no single field's index can
capture the relationship.

Approaches from database theory:

- **Sort-merge join:** Sort values by the left field, then scan for
  right-field matches.  Cost: `O(n log n)` build, `O(n)` query.
- **Hash join:** Hash the left field values, probe with right field values.
  Cost: `O(n)` expected.

For compile-time guard analysis, cross-field constraints map to M8
(Multi-Tape Automaton) from the main document §7.6: each field corresponds
to a tape, and the automaton coordinates constraints across tapes.

---

## 6. Container Element Constraints

### 6.1 Existential: Inverted Indexes

For guards asserting that some element satisfies a predicate —
`any(items, |x| x.price < 100)` — the dispatch question is: does the
container have at least one element in the range `[0, 100)`?

An **inverted index** reverses the containment relationship: instead of
mapping containers to elements, map value ranges to the set of containers
having elements in that range.

```
  Forward:   container₁ → [42, 87, 150]
             container₂ → [10, 200]
             container₃ → [99, 101]

  Inverted:  [0, 100)   → {container₁, container₂, container₃}
             [100, 200) → {container₁, container₂, container₃}
             [200, ∞)   → {container₂}
```

A point query "which containers have an element `< 100`?" reduces to a
range lookup in the inverted index: `O(log m + k)` where `k` is the
output size.

### 6.2 Universal: Bloom Filter Pre-Check

For guards asserting that every element satisfies a predicate —
`all(nodes, |n| n.safe)` — a single violating element falsifies the guard.

A **Bloom filter** (Bloom, 1970) provides probabilistic pre-checking:
maintain a Bloom filter of elements that violate the predicate.  If the
filter reports no violations, the guard is likely satisfied (Bloom filters
have no false negatives for membership, which means no false positives for
"all elements safe").  A positive Bloom hit triggers a full scan.

Cost: `O(k)` for `k` hash functions per query (typically `k = 3`), with
a false positive rate of approximately `(1 - e^(-kn/m))^k` for `n`
elements and `m` filter bits.

### 6.3 Cardinality: Counting Indexes

For guards asserting that a minimum number of elements satisfy a predicate —
`count(items, |x| x > 0) ≥ 3` — maintain a per-container count of
qualifying elements.

A **counting index** stores `count_φ(container)` for each container and
predicate `φ` of interest.  The count is maintained incrementally: `O(1)`
update per element insertion/deletion.  Dispatch cost: `O(1)` — compare the
count against the threshold.

### 6.4 Positional: Position-Keyed Indexes

For guards constraining a specific position — `list[2] = "foo"` — treat
the position as a field path and apply the nested indexing approach from
§5.2.

### 6.5 Watched Literals for Dynamic Guard Sets

When guard predicates involve variables that change at runtime (e.g.,
channels with mutable state), the **two-watched-literal scheme** from SAT
solving (Moskewicz et al., 2001) provides amortized `O(1)` propagation.

**Intuition.** For a guard `φ` over variables `x₁, …, xₖ`, "watch" two
variables that currently satisfy their local constraints.  When a variable
changes, check only the guards that watch it.  If a watched variable no
longer satisfies its constraint, find a replacement; if none exists, the
guard may fire (or be falsified).  Guards whose watched variables haven't
changed are **never re-evaluated** — amortized `O(1)` per irrelevant change.

This is directly applicable to MeTTaIL's runtime: when a channel's message
pool changes (messages arrive or are consumed), guards watching that channel
are re-evaluated, but guards on unaffected channels are skipped entirely.
The watched-literal scheme formalizes this "only re-check what changed"
principle.

**Adaptation to guard dispatch.** Each guard watches two of its most
discriminating sub-predicates.  When a message arrives, only guards whose
watched predicates could be affected by the new value are checked.  For
channels with many guards but infrequent changes, this reduces per-message
dispatch cost from `O(m)` to `O(affected)`.

---

## 7. Composed and Cross-Domain Dispatch

### 7.1 Cascading Indexes by Selectivity

For guards combining constraints from independent domains —
`x ≥ 10 ∧ name = "foo"` — the `ProductAlgebra` (main document §9.1) proves
correctness but doesn't prescribe an evaluation order.

**Selectivity** is the fraction of values matching a predicate: lower
selectivity means fewer matches (more discriminating).  A **cascading
index** evaluates the most selective component first, pruning early:

```
╔══════════════════════════════════════════════════════════════════════════╗
║  CASCADE_DISPATCH(guards: [(φ₁ᴬ, φ₁ᴮ), …, (φₘᴬ, φₘᴮ)],                ║
║                   selectivity: [sᴬ, sᴮ],                                ║
║                   value: (vᴬ, vᴮ)) → Vec<GuardId>                       ║
║                                                                          ║
║  Dispatch a product-domain value through cascading indexes.              ║
║                                                                          ║
║  ── Order by selectivity ──────────────────────────────────────────────  ║
║                                                                          ║
║  if sᴬ < sᴮ:        ▷ A is more selective (fewer matches)               ║
║      outer ← index_A;  inner ← index_B                                  ║
║  else:                                                                   ║
║      outer ← index_B;  inner ← index_A                                  ║
║                                                                          ║
║  ── Cascade ───────────────────────────────────────────────────────────  ║
║                                                                          ║
║  candidates ← outer.query(v_outer)      ▷ O(log m) or O(1)              ║
║  results ← []                                                            ║
║  for guard_id in candidates:                                             ║
║      if inner.matches(guard_id, v_inner):  ▷ check only candidates       ║
║          results.push(guard_id)                                          ║
║  return results                                                          ║
║                                                                          ║
║  Expected cost: O(query_outer + |candidates| · query_inner)              ║
║  When outer is selective: |candidates| ≪ m → much cheaper than O(m)     ║
╚══════════════════════════════════════════════════════════════════════════╝
```

The M7 Probabilistic Automaton (main document §7.6) provides the
selectivity estimates that drive cascade ordering.

### 7.2 Trie Composition for Decomposition Guards

For string decomposition guards `x · y = "cowboy"` (§4.3), the composed
trie automata `T_prefix ⊗ T_suffix` is a special case of `ProductAlgebra`
where each component is a trie-based algebra over string prefixes/suffixes.

The composition generalizes beyond strings:

| Decomposition guard | Trie composition |
|---|---|
| `x · y = "cowboy"` (string split) | Prefix trie ⊗ suffix trie |
| `x · y · z = "cowboy"` (3-way split) | Prefix ⊗ infix ⊗ suffix |
| `reverse(x) = y` | Forward trie ⊗ reverse trie |
| `x ++ y = [1,2,3,4,5]` (list split) | List prefix trie ⊗ list suffix trie |
| `f(x) = y` (function guard) | Domain trie ⊗ range trie (SFT pre-image) |

### 7.3 SFT Composition for Transformation Guards

For guards involving transformations — `normalize(name) = "foo"` — the M15
SFT module (main document §7.6) computes the pre-image: which raw inputs
produce normalized outputs matching the guard?

When multiple transformations are chained (`normalize ∘ trim ∘ lowercase`),
**SFT composition** (Veanes et al., 2012) produces a single composed SFT
at compile time.  The runtime cost is a single traversal of the composed
transducer — no intermediate string materialization.

---

## 8. Predicate Indexing from Logic Programming

### 8.1 WAM First-Argument Indexing

The **Warren Abstract Machine** (WAM) indexes Prolog clauses by the
principal functor of the first argument.  When a query `?- f(a, X)` arrives,
only clauses whose first argument could unify with `a` are tried.

In MeTTaIL, this corresponds to Layer 1 (structural dispatch): the decision
tree trie branches on the outermost constructor of the received value.

**Limitation:** First-argument indexing ignores deeper structure and
non-first arguments.  A guard `@{App(_, Var(x))}` that constrains only the
second argument would not benefit.

### 8.2 Deep and Multi-Argument Indexing

**YAP Prolog** (Costa et al., 2007) implements deep indexing: the index
descends into nested constructor paths, not just the first argument.
**SWI-Prolog** (Wielemaker, 2011) adds JIT indexing: indexes are built on
demand based on observed query patterns, adapting to the workload.

MeTTaIL's PathMap byte trie already supports deep path indexing — it
encodes arbitrarily nested field access paths as byte sequences.  Extending
PathMap from parse dispatch to guard dispatch would give deep multi-argument
indexing for structural guards.

### 8.3 Path Indexing and Code Trees

**Path indexing** (Stickel, 1989) flattens a term's tree structure into a
set of root-to-leaf path strings.  The index is a trie over these paths,
mapping each path to the set of patterns containing it.  Query time:
`O(|t| + output)` — one trie lookup per term position.

**Code trees** (Voronkov, 1995) compile a set of clause heads into a
virtual machine program: each instruction tests a position and branches
on the constructor.  This is the discrimination tree from §5.1 compiled
to executable code rather than interpreted as a data structure — the same
principle as MeTTaIL's decision tree codegen (main document §2.6).

### 8.4 Feature Vector Pre-Filtering

Before detailed structural matching, compute a cheap **feature vector** for
each term — a numeric summary capturing structural properties (root
constructor ID, arity, depth, set of constructor names).  Use the feature
vector to **pre-filter** candidates: only patterns whose feature vector is
compatible with the term's are tried.

This is analogous to the existing Bloom filter pre-check in MeTTaIL's
pattern index (`pattern_trie.rs`), extended from constructor-set Bloom
filters to multi-feature vectors.  The M9 Multiset Automaton's feature
multiplicities (main document §7.6) already compute a form of feature
vector — generalizing this to structural guards is architecturally natural.

### 8.5 RETE Networks for Dynamic Guard Sets

The **RETE algorithm** (Forgy, 1982) is the classical approach for
efficiently matching multiple rules against a changing working memory in
production systems:

- **Alpha network:** Single-condition tests.  Each alpha node tests one
  field of a fact; alpha memories store facts passing that test.
- **Beta network:** Join conditions across multiple facts.  Beta nodes
  join alpha memories on shared variables; beta memories store partial
  matches.
- **Production nodes:** Rules that fire when all conditions are satisfied.

The key property: RETE is **incremental** — when a fact is added or removed,
only the affected parts of the network are re-evaluated.  Common conditions
across rules share nodes and memories.

**MeTTaIL connection:** When a channel has many guarded receives with shared
sub-predicates (e.g., multiple guards sharing `safe(x)` but differing in
other conditions), a RETE-like network shares the `safe(x)` evaluation
across all guards.  This is particularly relevant for Ascent's behavioral
predicate layer (Layer 3): Ascent's hash-indexed relations are already a
form of alpha memory, and join patterns across multiple channels are beta
joins.

The **LEAPS** variant (lazy RETE) defers join computation until a rule is
about to fire — reducing memory and avoiding speculative join computation.
This maps to MeTTaIL's two-phase guard evaluation: structural matching
(Layer 2) acts as the alpha filter, and behavioral predicates (Layer 3)
act as lazy beta joins that execute only for structurally-matching candidates.

---

## 9. Unified Dispatch Architecture

The indexing structures from §§2-8 can be composed into a **multi-level
dispatch pipeline** that progressively narrows the candidate set:

```
  Message @(q) arrives on channel n
       │
       ▼
  ┌──────────────────────────────────────────────────────────────────┐
  │ Level 0: Feature vector pre-filter                                │
  │ Bit-parallel check on term features eliminates clearly            │
  │ non-matching guards.  Cost: O(1).                                 │
  └────────────────────────────┬─────────────────────────────────────┘
                               │ candidates reduced
                               ▼
  ┌──────────────────────────────────────────────────────────────────┐
  │ Level 1: Structural dispatch (existing, implemented)              │
  │ Decision tree trie / computed goto on outermost constructor.     │
  │ Cost: O(|path|).                                                  │
  └────────────────────────────┬─────────────────────────────────────┘
                               │ category + rule candidates
                               ▼
  ┌──────────────────────────────────────────────────────────────────┐
  │ Level 2: Domain-specific index (proposed, §§3-6)                  │
  │ Segment tree (numeric), trie (string), discrimination tree (ADT), │
  │ inverted index (container).  Cost: O(log m) per domain.          │
  └────────────────────────────┬─────────────────────────────────────┘
                               │ guard candidates
                               ▼
  ┌──────────────────────────────────────────────────────────────────┐
  │ Level 3: Behavioral predicates (existing, implemented)            │
  │ Ascent fixpoint relation lookups.  Cost: O(1) per predicate.     │
  └────────────────────────────┬─────────────────────────────────────┘
                               │ matching guards
                               ▼
                        Dispatch result
```

Levels 0 and 2 are the new contributions.  They slot between the existing
Levels 1 and 3, reducing the candidate set that Level 3 must evaluate.

The compile-time pipeline (main document §2.5, stages 1-6) would be
extended: after minterm computation (stage 5), an index construction pass
selects the appropriate index structure for each guard domain and builds it.
The codegen stage (6) emits the index-aware dispatch code.

---

## 10. Complexity Summary

| Guard domain | Current (minterms) | Proposed structure | Proposed query | Preconditions |
|---|---|---|---|---|
| 1D integer interval | `O(m)` boundary tests | Segment tree | `O(log m + k)` | `k = 1` variable |
| 1D bounded integer | `O(m)` | vEB tree | `O(log log U)` | Known universe `U` |
| 2D linear (halfplane) | `O(m)` | BSP tree | `O(log m)` | `k = 2` variables |
| k-D bounding box | `O(m)` | R-tree | `O(log m + k)` | Axis-aligned constraints |
| Exact string | `O(m · \|s\|)` | Hash table / trie | `O(\|s\|)` | Exact equality |
| String prefix | `O(m · \|p\|)` | Prefix trie | `O(\|p\|)` | Prefix predicate |
| String decomposition | `O(m · \|t\|)` | Composed trie ⊗ | `O(\|x\| + \|y\|)` | Known target |
| Multi-regex | `O(m · \|s\|)` | Aho-Corasick / SFA product | `O(\|s\| + output)` | Literal or regex |
| Constructor pattern | `O(m · \|t\|)` | Discrimination tree | `O(\|t\| + output)` | Term patterns |
| Nested field | `O(m)` | Nested index | `O(\|path\| + log m)` | Field path + value |
| Existential container | `O(n · m)` | Inverted index | `O(log m + k)` | Element predicate |
| Universal container | `O(n · m)` | Bloom + scan | `O(k) + O(n)` worst | Element predicate |
| Cardinality | `O(n · m)` | Counting index | `O(1)` | Maintained incrementally |
| Product domain | `O(m₁ · m₂)` | Cascading index | `O(query₁ + \|cand\| · query₂)` | Selectivity estimates |

**When indexing helps:** Channels with many competing guards (`m > 20`),
guards over structured data (ADTs, containers), or guards spanning
heterogeneous domains.

**When it doesn't:** Channels with few guards (`m ≤ 5`) — the constant
factors of index construction outweigh the query savings.  Simple Boolean
guards (T1-tier) — eliminated at compile time, no runtime cost.

---

## 11. Open Questions

1. **Adaptive runtime indexing.** Instead of choosing index structures at
   compile time, build them incrementally at runtime as queries arrive —
   mirroring SWI-Prolog's JIT indexing approach.  This would benefit
   channels where the guard population changes dynamically.

2. **Learned indexes.** Recent work (Kraska et al., 2018) replaces B-trees
   with ML models trained on the data distribution.  For workloads with
   strong distributional patterns (e.g., most messages are small integers),
   a learned model could outperform traditional indexes.

3. **Nominal indexing.** For guards involving name freshness (M6 Register
   Automaton), orbit-finite nominal sets (Bojańczyk et al.) offer
   symmetry-aware indexing that avoids enumerating name permutations.

4. **Index composition soundness.** The cascading index (§7.1) assumes
   component indexes are independent.  When guards share variables across
   domains (e.g., `x ≥ 10 ∧ len(name) = x`), the cascade must account for
   the dependency.  Formalizing when cascading is sound requires extending
   the `ProductAlgebra` theory.

---

## 12. References

1. Aho, A. V. & Corasick, M. J. (1975). ["Efficient string
   matching."](https://doi.org/10.1145/360825.360855) *Communications of
   the ACM*, 18(6):333-340.
   DOI: [10.1145/360825.360855](https://doi.org/10.1145/360825.360855).

2. Bloom, B. H. (1970). ["Space/time trade-offs in hash coding with
   allowable errors."](https://doi.org/10.1145/362686.362692)
   *Communications of the ACM*, 13(7):422-426.
   DOI: [10.1145/362686.362692](https://doi.org/10.1145/362686.362692).

3. D'Antoni, L. & Veanes, M. (2017). ["The power of symbolic automata and
   transducers."](https://doi.org/10.1007/978-3-319-63387-9_3) *CAV 2017*,
   LNCS 10427, pp. 47-67. Springer.
   DOI: [10.1007/978-3-319-63387-9_3](https://doi.org/10.1007/978-3-319-63387-9_3).

4. de Berg, M., Cheong, O., van Kreveld, M. & Overmars, M. (2008).
   [*Computational Geometry: Algorithms and
   Applications*](https://doi.org/10.1007/978-3-540-77974-2). 3rd ed.
   Springer.
   DOI: [10.1007/978-3-540-77974-2](https://doi.org/10.1007/978-3-540-77974-2).

5. Graf, P. (1995). ["Substitution tree
   indexing."](https://doi.org/10.1007/3-540-59200-8_52) *RTA 1995*, LNCS
   914, pp. 117-131. Springer.
   DOI: [10.1007/3-540-59200-8_52](https://doi.org/10.1007/3-540-59200-8_52).

6. Kraska, T., Beutel, A., Chi, E. H., Dean, J. & Polyzotis, N. (2018).
   ["The case for learned index
   structures."](https://doi.org/10.1145/3183713.3196909) *Proceedings of
   SIGMOD*, pp. 489-504. ACM.
   DOI: [10.1145/3183713.3196909](https://doi.org/10.1145/3183713.3196909).

7. Sekar, R., Ramakrishnan, I. V. & Voronkov, A. (2001). ["Term
   Indexing."](https://doi.org/10.1016/B978-044450813-3/50028-X) In
   *Handbook of Automated Reasoning*, vol. 2, ch. 26, pp. 1853-1964.
   Elsevier.
   DOI: [10.1016/B978-044450813-3/50028-X](https://doi.org/10.1016/B978-044450813-3/50028-X).

8. Selinger, P. G., Astrahan, M. M., Chamberlin, D. D., Lorie, R. A. &
   Price, T. G. (1979). ["Access path selection in a relational database
   management system."](https://doi.org/10.1145/582095.582099) *Proceedings
   of SIGMOD*, pp. 23-34. ACM.
   DOI: [10.1145/582095.582099](https://doi.org/10.1145/582095.582099).

9. Forgy, C. L. (1982). "Rete: A fast algorithm for the many pattern/many
   object pattern match problem." *Artificial Intelligence*,
   19(1):17-37.

10. Moskewicz, M. W., Madigan, C. F., Zhao, Y., Zhang, L. & Malik, S.
    (2001). "Chaff: Engineering an efficient SAT solver." *Proceedings of
    DAC*, pp. 530-535. ACM.

11. Veanes, M., Hooimeijer, P., Livshits, B., Molnar, D. & Bjørner, N.
    (2012). ["Symbolic finite state transducers: Algorithms and
    applications."](https://doi.org/10.1145/2103621.2103674) *Proceedings
    of POPL*, pp. 137-150. ACM.
    DOI: [10.1145/2103621.2103674](https://doi.org/10.1145/2103621.2103674).

12. Wang, X., Hong, Y., Chang, H., Park, K., Langdale, G., Hu, J. &
    Zhu, H. (2019). "Hyperscan: A fast multi-pattern regex matcher for
    modern CPUs." *Proceedings of NSDI*, pp. 631-648. USENIX.
