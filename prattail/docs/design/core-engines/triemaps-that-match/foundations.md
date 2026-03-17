# Theoretical Foundations: From "Triemaps that Match" to PraTTaIL

This document connects the theoretical framework of *Triemaps that Match* (Peyton Jones & Graf, 2022/2024) to PraTTaIL's implementation, explaining how the paper's key ideas manifest in Rust across the codebase.

**Prerequisites:** Basic familiarity with tries, pattern matching, and lambda calculus.

---

## 1. The Problem: Finite Maps Keyed by Syntax Trees

The fundamental challenge that motivates this entire architecture: given a collection of syntax tree patterns (e.g., equation LHS patterns, parse rule prefixes), we need a data structure that supports:

1. **Exact lookup** — given a concrete term `t`, find all patterns that equal `t`
2. **Matching lookup** — given a concrete term `t`, find all patterns `p` such that some substitution `σ` makes `σ(p) = t`
3. **Algebraic composition** — given two maps `M₁` and `M₂`, compute their union, intersection, and difference

### Why Hash Maps and Balanced Trees Fail

| Data structure | Exact lookup | Matching lookup | Composition |
|----------------|:----------:|:--------------:|:-----------:|
| `HashMap<Expr, V>` | O(k) amortized | Impossible | O(n) |
| `BTreeMap<Expr, V>` | O(k log n) | Impossible | O(n log n) |
| **Triemap** | **O(k)** | **O(k)** | **O(min(m,n))** |

where `k` = key size, `n` = map size.

The critical insight is that hash maps and balanced trees treat keys as *opaque atoms*. When a key contains a pattern variable (e.g., `f(x, y)` where `x` is a variable that matches anything), there is no way to perform matching lookup — you would have to enumerate all possible substitutions.

Tries, by contrast, decompose keys into their structure. A node at depth `d` in the trie corresponds to position `d` in the key. Pattern variables at position `d` match any byte at that position, enabling O(k) matching lookup by walking the trie with "wildcard" steps.

### The Paper's Key Insight

Peyton Jones & Graf observe that a triemap keyed by syntax trees has a *nested structure* mirroring the grammar itself (§2.3):

```haskell
data ExprMap v = EM
  { em_var  :: Map Var v      -- entries keyed by a variable
  , em_app  :: ExprMap (ExprMap v)  -- entries keyed by App(f, x)
  , em_lam  :: ExprMap v      -- entries keyed by Lam(body)
  }
```

This is recursive: the `em_app` field is itself an `ExprMap`, nested one level deeper. Looking up `App(f, x)` first descends into `em_app`, looks up `f` to get an inner `ExprMap`, then looks up `x` in that inner map.

---

## 2. From Haskell ExprMap to Rust PathMap

PraTTaIL does **not** use the Haskell-style nested record approach directly. Instead, it uses **PathMap** — a persistent radix-256 trie indexed by *byte-encoded paths*.

The key bridge: the paper's nested `ExprMap` field lookups correspond 1:1 to bytes in a flattened byte-path encoding. Instead of `em_app → lk(f) → lk(x)`, PraTTaIL encodes the entire key as a byte sequence `[arity_byte, symbol_bytes..., arg₁_bytes..., arg₂_bytes...]` and inserts it into a flat trie.

### Correspondence Table

| Haskell ExprMap field | Byte encoding | PathMap role |
|-----------------------|--------------|--------------|
| `em_var :: Map Var v` | `0xC0` (NewVar) or `0x80|slot` (VarRef) | Pattern variables in pattern trie |
| `em_app :: ExprMap (ExprMap v)` | `Arity(n)` + `SymbolSize(s)` + name + args | Nesting via byte prefix extension |
| `em_lam :: ExprMap v` | `0x48` (Lambda) + binder_slot + body | PraTTaIL extension tag |
| Union (`unionEM`) | `pjoin` (⊔) | Lattice trait method |

### Advantages of Byte-Path Flattening

1. **Generic trie**: One `PathMap<V>` implementation handles all expression types via encoding, rather than a bespoke nested struct per grammar.
2. **Prefix sharing**: Common byte prefixes share trie nodes automatically, regardless of where the nesting boundary falls.
3. **Lattice algebra**: PathMap's `Lattice` and `DistributiveLattice` traits give us `pjoin`/`pmeet`/`psubtract` for free, enabling grammar composition analysis.
4. **Arc-based persistence**: Copy-on-write structural sharing enables efficient immutable snapshots.

---

## 3. Alpha-Equivalence via De Bruijn Numbering

The paper devotes §4 to the alpha-equivalence problem: `λx.f(x,x)` and `λy.f(y,y)` must map to the same trie path. The solution is De Bruijn canonicalization — replacing variable names with introduction-order indices.

### The Paper's Approach (§4.2)

The paper introduces `DBEnv` (tracking bound variable depth), `BoundKey` (a de Bruijn index), and `AlphaExpr` (the canonicalized expression type). Each variable reference is replaced by its binding distance.

### PraTTaIL's Adaptation

PraTTaIL's `EncodingEnv` (`macros/src/logic/pattern_codec.rs:73-122`) tracks variables by *introduction order* in pre-order traversal rather than by binding depth:

```rust
struct EncodingEnv {
    var_slots: HashMap<String, u8>,  // name → slot index
    next_slot: u8,                   // next available slot
}
```

The first occurrence of any variable emits `NewVar` (`0xC0`); subsequent occurrences emit `VarRef(slot)` (`0x80 | slot`). This scheme:

- Assigns slot 0 to the first variable encountered, slot 1 to the second, etc.
- Uses introduction-order rather than binding-depth (De Bruijn levels, not indices)
- Is compatible with MORK's encoding (see §6)
- Handles binder scoping via `introduce_binder()` / `restore_binder()` for lambda patterns

### Alpha-Equivalence Guarantee

> **Theorem.** `encode(p) = encode(q)` if and only if `p ≡α q`.

*Proof sketch.* The encoding is a deterministic function of the pattern's tree structure with variables replaced by introduction-order indices. Two patterns are alpha-equivalent iff they differ only in variable names. Since the encoding erases names and assigns indices by traversal order, alpha-equivalent patterns produce identical bytes, and non-alpha-equivalent patterns produce different bytes (different structure → different arity/symbol bytes; same structure but different variable binding → different slot indices). ∎

---

## 4. Matching Lookup

This is the paper's central contribution (§5). Not only can we look up *exact* keys in the trie, but we can look up *patterns* — keys containing pattern variables that match any sub-expression.

### The Paper's Mechanism (§5.1–5.3)

The paper adds a `mm_pvar` field to each `MatchME` level:

```haskell
data MatchME v = MME
  { mm_evar :: Map Var v       -- variable patterns (x matches any expr)
  , mm_app  :: MatchME (MatchME v)
  , mm_lam  :: MatchME v
  , mm_pvar :: Map PatVar v    -- pattern variables stored at this level
  }
```

Looking up a concrete expression `e` in a `MatchME` checks both the structural path (via the nested fields) and the pattern variable field `mm_pvar` (matching any expression at this point).

### PraTTaIL's Implementation

PraTTaIL uses two complementary mechanisms that together achieve the same effect:

**1. Pattern Trie** (`macros/src/logic/pattern_trie.rs`):

The `PatternIndex` stores equation/rewrite patterns in a `PathMap<RuleIdSet>` indexed by De Bruijn bytes. The trie's structural prefix sharing means that two patterns sharing a constructor prefix share trie nodes:

```rust
pub struct PatternIndex {
    pub lhs_trie: PathMap<RuleIdSet>,    // LHS pattern bytes → rule IDs
    pub rhs_trie: PathMap<RuleIdSet>,    // RHS pattern bytes → rule IDs
    pub lhs_bloom: BloomFilter,          // O(1) negative rejection
    pub constructor_sets: HashMap<RuleId, HashSet<String>>,
    pub lhs_bytes: HashMap<RuleId, Vec<u8>>,
    pub rule_count: usize,
}
```

**2. Bloom Filter Pre-check** (`macros/src/logic/bloom_filter.rs`):

Before descending into the PathMap, a bloom filter provides O(1) negative rejection. This corresponds to the paper's observation (§5.4) that matching lookup should short-circuit early when no pattern can possibly match.

**3. Subsumption Detection** (`macros/src/logic/pattern_trie.rs:362-408`):

PraTTaIL extends the paper's matching lookup to detect *subsumption*: pattern `P` subsumes pattern `Q` if `P` matches every term that `Q` matches. In De Bruijn encoding, this corresponds to `P` having a variable (`NewVar`/`VarRef`) where `Q` has concrete structure. This is a compile-time lint, not a runtime operation.

### Complexity

- **Exact lookup**: O(k) where k = encoded key length
- **Matching lookup** (via pattern variables): O(k) per pattern candidate (bloom filter rejects non-matches in O(1))
- **Subsumption detection**: O(n²·k) where n = number of patterns (pairwise comparison)

---

## 5. Lattice Algebra for Grammar Composition

The paper discusses `unionEM` and `unionWithEM` (§3.4) for combining triemaps. PraTTaIL extends this to a full distributive lattice.

### From Union to Distributive Lattice

| Paper operation | PathMap method | Semantic meaning |
|-----------------|---------------|------------------|
| `unionEM` | `pjoin` (⊔) | Merge two grammars: keep all rules from both |
| — | `pmeet` (⊓) | Intersect: keep only rules shared by both |
| — | `psubtract` (∖) | Difference: rules in A but not B |

The lattice operations satisfy:

- **Commutativity**: `a ⊔ b = b ⊔ a` and `a ⊓ b = b ⊓ a`
- **Associativity**: `(a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)`
- **Idempotence**: `a ⊔ a = a` and `a ⊓ a = a`
- **Absorption**: `a ⊔ (a ⊓ b) = a` and `a ⊓ (a ⊔ b) = a`
- **Distributivity**: `a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)`

PraTTaIL exploits these for grammar composition analysis (`decision_tree.rs:2054`):

```rust
pub fn composition_trie_analysis(
    tree_a: &CategoryDecisionTree,
    tree_b: &CategoryDecisionTree,
) -> CompositionTrieReport {
    let common   = tree_a.segments[0].meet(&tree_b.segments[0]);    // A ⊓ B
    let unique_a = tree_a.segments[0].subtract(&tree_b.segments[0]); // A ∖ B
    let unique_b = tree_b.segments[0].subtract(&tree_a.segments[0]); // B ∖ A
    let merged   = tree_a.segments[0].join(&tree_b.segments[0]);     // A ⊔ B
    // ...
}
```

This answers three questions about grammar composition in a single analysis pass:
1. **Shared rules** (meet): which parse dispatch paths exist in both grammars?
2. **Unique rules** (subtract): what does each grammar add beyond the other?
3. **New ambiguities** (join): does merging introduce dispatch conflicts?

---

## 6. Lineage: Paper → MORK → MeTTaTron → PraTTaIL

### MORK: The MeTTa Optimal Reduction Kernel

MORK (located at `/home/dylon/Workspace/f1r3fly.io/MORK/`) is a byte-encoded hypergraph rewriting engine that directly implements the "triemaps that match" concepts. Its `expr/src/lib.rs` uses an identical 2-bit tag byte scheme:

```text
0b00_aaaaaa (0x00-0x3F)  Arity(a)     — constructor with a children
0b10_iiiiii (0x80-0xBF)  VarRef(i)    — reference to i-th variable
0b11_000000 (0xC0)       NewVar       — introduce a fresh variable
0b11_ssssss (0xC1-0xFE)  SymbolSize   — next s bytes are constructor name
```

MORK uses PathMap as both storage and query engine at runtime — expressions live in the trie, and rewriting is implemented as trie operations (matching lookup to find redexes, insertion to add reduct).

### MeTTaTron: Dual-Tier Storage

MeTTaTron (the MeTTa compiler at `/home/dylon/Workspace/f1r3fly.io/MeTTa-Compiler/`) uses a dual-tier approach:
- **Ground atoms** (no variables): stored in a PathMap trie for O(k) lookup
- **Variable atoms** (contain pattern variables): stored in a `Vec` for linear scan

This is the paper's `mm_pvar` idea in practice — pattern variables are stored separately because they match anything at their position.

### PraTTaIL: Compile-Time Triemaps

PraTTaIL's key innovation is using triemaps at **compile time** rather than runtime:

| System | Trie role | When |
|--------|-----------|------|
| MORK | Runtime storage + query | Execution |
| MeTTaTron | Runtime storage (ground tier) | Execution |
| **PraTTaIL** | **Compile-time analysis + code generation** | **Macro expansion** |

PraTTaIL builds PathMap tries during `language!` macro expansion to:
1. Construct **decision trees** for parse dispatch (byte-encoded token prefixes → rules)
2. Build **pattern indexes** for equation/rewrite stratification (De Bruijn bytes → rule groups)
3. Perform **grammar composition analysis** (lattice operations on decision trees)

The output is not a runtime trie but **generated match arms** (4-8x faster per dispatch step than runtime trie walk). The trie serves as a compile-time analysis tool, and the results are baked into the generated Rust code.

PraTTaIL also extends MORK's tag scheme with `0b01_tttttt` extension tags (0x40-0x4B) for collections, lambdas, substitutions, maps, and zips — constructs that do not exist in MORK's simpler expression language.

---

## References

1. **Peyton Jones, S. & Graf, S.** (2022/2024). "Triemaps that match." arXiv:2302.08775. — The foundational paper defining ExprMap, matching lookup, and De Bruijn leveling for triemaps.

2. **Hinze, R.** (2000). "Generalizing Generalized Tries." *Journal of Functional Programming* 10(4), 327-351. — Earlier work on type-indexed tries that motivated ExprMap.

3. **Connelly, R. H. & Morris, F. L.** (1995). "A Generalization of the Trie Data Structure." *Mathematical Structures in Computer Science* 5(3), 381-418. — Original generalized trie theory.

4. **de Bruijn, N. G.** (1972). "Lambda calculus notation with nameless dummies, a tool for automatic formula manipulation." *Indagationes Mathematicae* 75(5), 381-392. — The De Bruijn index scheme used for alpha-equivalence.

5. **Sekar, R., Ramakrishnan, I. V. & Voronkov, A.** (2001). "Term Indexing." In *Handbook of Automated Reasoning*, Ch. 26. — Comprehensive survey of discrimination trees, path indexing, and related term indexing techniques.

---

## Key Source Files

| File | Role |
|------|------|
| `prattail/src/decision_tree.rs` | Parse dispatch via PathMap tries |
| `macros/src/logic/pattern_codec.rs` | De Bruijn byte encoding |
| `macros/src/logic/pattern_trie.rs` | PatternIndex (PathMap + bloom filter) |
| `macros/src/logic/bloom_filter.rs` | O(1) negative rejection |
| External: PathMap crate | Persistent radix-256 trie with lattice algebra |
| External: MORK `expr/src/lib.rs` | MORK-compatible byte encoding |

---

**Next:** [PathMap Overview](pathmap-overview.md) — deep dive into the PathMap data structure, lattice traits, and zipper API.
