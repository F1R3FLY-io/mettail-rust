# PraTTaIL to Ascent: Codegen Optimizations

**Date:** 2026-02-21

## 1. Pipeline Context

PraTTaIL is the parser generator component of MeTTaIL. The `language!` macro invocation flows through two parallel code generation paths:

1. **PraTTaIL parser generation** — produces a Pratt + recursive descent parser
2. **Ascent Datalog generation** — produces an Ascent program for semantic analysis

This document describes four optimizations applied to the Ascent code generation path, their locations in the codebase, and links to their formal correctness proofs.

```
language! { ... }
    │
    ├──── PraTTaIL Pipeline ────────────> Parser (TokenStream)
    │     (prattail/src/)
    │
    └──── Ascent Code Gen ──────────────> Ascent Program (TokenStream)
          (macros/src/logic/, macros/src/gen/runtime/)
              │
              ├── Opt 2: TLS Vec Pool (common.rs)
              ├── Opt 3: Dead Rule Pruning (common.rs + categories.rs)
              ├── Opt 4: OrdVar/Scope Ordering (runtime/src/binding.rs)
              └── Opt 5: SCC Splitting (common.rs + language.rs)
```

## 2. Where Ascent Code Is Generated

### 2.1 Logic Modules (`macros/src/logic/`)

| Module | Responsibility |
|--------|---------------|
| `mod.rs` | Top-level Ascent source assembly (`AscentSourceOutput`) |
| `common.rs` | Shared helpers, reachability, core categories, TLS pool |
| `helpers.rs` | Consolidated deconstruction and congruence rules |
| `categories.rs` | Category exploration and dead rule pruning |
| `congruence.rs` | Equation congruence rules |
| `equations.rs` | User-defined equation rules |
| `rules.rs` | User-defined rewrite rules |

### 2.2 Runtime Modules

| Module | Responsibility |
|--------|---------------|
| `macros/src/gen/runtime/language.rs` | Language struct, Ascent struct generation, SCC dispatch |
| `runtime/src/binding.rs` | OrdVar wrapper, Scope wrapper (Hash + Ord) |

## 3. Opt 2: TLS Vec Pool Iteration Equivalence

**Problem:** Each subterm extraction rule creates a `vec![]` heap allocation in the Ascent fixpoint inner loop.

**Solution:** Replace `vec![...]` with a thread-local `Cell<Vec<T>>` pool. The buffer is taken, cleared, filled, and returned — zero allocation after the first call.

**Code location:**
- `common.rs:448-482` — `generate_tls_pool_iter()`: generates the TLS pool pattern
- `common.rs:397-406` — `PoolArm` struct: match arm specification

**Key invariant:** After `clear()`, the prior pool contents are discarded. The `push` operations build the same sequence as `vec![]`. Uses `Cell<Vec<T>>` (not `RefCell`) to avoid re-entrancy panics from nested dispatch calls.

**Full proof:** [docs/design/made/ascent-optimizations/tls-pool-equivalence.md](../../../docs/design/made/ascent-optimizations/tls-pool-equivalence.md)

## 4. Opt 3: Dead Rule Pruning (Reachability-Based)

**Problem:** Cross-category rules are generated for all `(src, tgt)` pairs. Many can never fire because no constructor path connects the source category to the target.

**Solution:** Build a category reachability graph from constructor field types. Compute the transitive closure. Skip rule generation for unreachable pairs.

**Code location:**
- `common.rs:215-298` — `compute_category_reachability()`: builds graph, computes transitive closure
- `common.rs:300-325` — `collect_type_refs()`: extracts category references from `TypeExpr`
- `categories.rs:34-48` — reachability check before rule generation

**Key invariant:** Auto-generated variants (`Apply`, `MApply`, `Lam`, `MLam`) are excluded from the base graph. They create edges between all pairs, which defeats pruning. Only user-defined constructor fields determine reachability.

**Full proof:** [docs/design/made/ascent-optimizations/dead-rule-pruning.md](../../../docs/design/made/ascent-optimizations/dead-rule-pruning.md)

## 5. Opt 4: OrdVar Total Order / Scope Total Preorder

**Problem:** Ascent uses BTree collections requiring `Ord`. The `moniker` crate's `Var` and `Scope` types lack `Ord`.

**Solution:** Two wrapper types with hash-based ordering:
- `OrdVar`: wraps `Var<String>`, provides total order via hash of `UniqueId`
- `Scope<P,T>`: wraps `moniker::Scope<P,T>`, provides total preorder via hash of pattern + body comparison

**Code location:**
- `runtime/src/binding.rs:256-289` — `OrdVar` struct and `Ord` implementation
- `runtime/src/binding.rs:87-134` — `Scope` struct, `Hash` and `Ord` implementations

**Key invariant:** `OrdVar` is a total order (reflexive, antisymmetric, transitive, total) under the `hash_uid_injective` assumption. `Scope` is a total preorder (reflexive, transitive, total — NOT antisymmetric due to hash collisions on patterns). BTree only requires total preorder.

**Full proof:** [docs/design/made/ascent-optimizations/ordvar-scope-ordering.md](../../../docs/design/made/ascent-optimizations/ordvar-scope-ordering.md)

## 6. Opt 5: SCC Splitting (Core/Full Fixpoint Equivalence)

**Problem:** Multi-category languages generate a single large Ascent struct. For common inputs (core-category terms), most rules target empty non-core relations.

**Solution:** Compute "core" categories (bidirectionally reachable from primary). Generate a smaller Core Ascent struct with only core-to-core rules. Route core-category inputs to the Core struct; non-core inputs to the Full struct.

**Code location:**
- `common.rs:357-391` — `compute_core_categories()`: identifies core categories
- `common.rs:327-340` — `CategoryFilter` type and `in_cat_filter()` helper
- `categories.rs:37-48` — further restricts reachable pairs to core-only for core struct
- `language.rs:1173-1312` — SCC-split dispatcher, core/full struct generation

**Key invariant:** For core-category inputs, non-core relations start empty (only core category is seeded) and remain empty throughout fixpoint iteration (S1). Core-target derivations are identical in both structs (S2). Therefore the fixpoints are identical when restricted to core categories (S3).

**Full proof:** [docs/design/made/ascent-optimizations/scc-splitting.md](../../../docs/design/made/ascent-optimizations/scc-splitting.md)

## 7. Data Flow Diagram

```
LanguageSpec
    │
    ├──── types ──────────────────────┐
    │                                 │
    │     compute_category_reachability()     ← Opt 3: builds graph
    │              │                  │
    │              ├── reachable set ──┤
    │              │                  │
    │     compute_core_categories()          ← Opt 5: SCC analysis
    │              │                  │
    │              └── core_cats ─────┤
    │                                 │
    ├──── terms ──────────────────────┤
    │                                 │
    │     generate_category_rules()          ← Opt 3: prune dead rules
    │     generate_tls_pool_iter()           ← Opt 2: zero-alloc iteration
    │              │                  │
    │              └── rules ─────────┤
    │                                 │
    ├──── runtime ────────────────────┤
    │                                 │
    │     OrdVar, Scope wrappers             ← Opt 4: ordering
    │     run_ascent_typed dispatcher        ← Opt 5: core/full routing
    │              │                  │
    │              └── ascent code ───┘
    │
    └──── TokenStream (parser + ascent)
```

## 8. References

### Documentation

- [Ascent Optimization Proofs — Overview](../../../docs/design/made/ascent-optimizations/README.md)
- [Opt 2: TLS Pool Equivalence](../../../docs/design/made/ascent-optimizations/tls-pool-equivalence.md)
- [Opt 3: Dead Rule Pruning](../../../docs/design/made/ascent-optimizations/dead-rule-pruning.md)
- [Opt 4: OrdVar/Scope Ordering](../../../docs/design/made/ascent-optimizations/ordvar-scope-ordering.md)
- [Opt 5: SCC Splitting](../../../docs/design/made/ascent-optimizations/scc-splitting.md)
- [Rocq Artifacts](../../../docs/design/made/ascent-optimizations/rocq-artifacts.md)
- [Rule Consolidation (Opt 1)](../../../docs/design/made/rule-consolidation/)

### Rocq Source

- `formal/rocq/ascent_optimizations/theories/` — 7 files, 1,790 lines, zero `Admitted`

### Architecture

- [PraTTaIL Architecture Overview](architecture-overview.md) — Parser generation pipeline
