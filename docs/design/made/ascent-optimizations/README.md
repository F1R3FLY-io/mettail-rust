# Ascent Runtime Optimization Proofs

## Executive Summary

Four performance optimizations applied to the PraTTaIL Ascent Datalog code generator have been formally verified in Rocq (Coq 9.1). Together they reduce allocation, prune dead rules, establish ordering invariants, and split fixpoint computation — all without changing the semantic output.

| Opt | Description | Key Theorem(s) | Rocq File | Lines |
|-----|-------------|-----------------|-----------|-------|
| 2 | TLS Vec Pool Iteration Equivalence | T1: `pool_equiv` | `TLSPoolEquiv.v` | 133 |
| 3 | Dead Rule Pruning (Reachability) | P2: `dead_rule_derives_nothing`, P3: `pruned_equals_full` | `DeadRulePruning.v` | 183 |
| 4 | OrdVar Total Order / Scope Preorder | O1a-d: `cmp_var_*`, O2a-c: `cmp_scope_*`, O3, O4 | `TotalOrder.v` | 425 |
| 5 | SCC Splitting (Core/Full Fixpoint) | S1: `non_core_derives_nothing`, S2: `core_derivations_equal`, S3: `fixpoint_restriction` | `SCCSplitting.v` | 362 |

**Total: 7 Rocq files, 1,790 lines, zero `Admitted`.**

## Context

The MeTTaIL compilation pipeline transforms a `language!` macro invocation into two artifacts:

1. A **PraTTaIL parser** (Pratt + recursive descent) for syntactic analysis
2. An **Ascent Datalog program** for semantic analysis (rewriting, equation solving, fold evaluation)

The Ascent program is the runtime workhorse. Its performance directly impacts evaluation latency. These four optimizations target the Ascent code generation path in `macros/src/logic/` and `macros/src/gen/runtime/language.rs`, reducing:

- **Heap allocation** per Datalog rule firing (Opt 2)
- **Rule count** by pruning rules that can never fire (Opt 3)
- **Ordering overhead** by providing correct `Ord` implementations (Opt 4)
- **Fixpoint iteration cost** by splitting into smaller SCC structs (Opt 5)

A prior optimization (Opt 1: Rule Consolidation) is documented separately in `docs/design/made/rule-consolidation/`.

## Proof Architecture

The 7 Rocq files form a dependency DAG:

```
                    Prelude.v
                   /    |    \
                  /     |     \
                 v      v      v
    TLSPoolEquiv.v  TotalOrder.v  GraphReachability.v
          |              |           /           \
          |              |          v              v
          |              |   DeadRulePruning.v  SCCSplitting.v
          |              |          |              |
          v              v          v              v
          +----------- ConcreteInstantiations.v --+
```

**Shared infrastructure** (`Prelude.v`, 146 lines):
- Hash function model with injectivity hypothesis (for `u32`-sized types)
- `hash_le` ordering derived from hash values with reflexivity, transitivity, totality, antisymmetry
- List utilities: `flat_map_nil`, `flat_map_cons`, `flat_map_app`, `flat_map_all_nil`, `flat_map_filter_nil`
- Conditional extraction (`cond_extract`) and decidable equality helpers
- Multiset equivalence notation (`l1 ≡ₘ l2 := Permutation l1 l2`)

**Graph infrastructure** (`GraphReachability.v`, 156 lines):
- Directed graph model with finite node set and decidable edge relation
- Reachability as reflexive-transitive closure (`reach_refl`, `reach_step`)
- Bidirectional reachability for SCC core computation (`bidi_reach`)
- Field type abstraction linking constructor fields to graph edges

## Concrete Instantiations

Each abstract theorem is instantiated for two concrete languages (`ConcreteInstantiations.v`, 385 lines):

**Calculator** (single category):
- One category (`Int`) with 6 constructors: `NumLit`, `Add`, `Sub`, `Mul`, `Div`, `Neg`
- Trivial reachability: `Int` reaches only itself
- Dead rule pruning is vacuously correct (no cross-category rules)
- Demonstrates: `calc_pool_equiv` (Opt 2), `calc_no_dead_rules` (Opt 3), `calc_ordvar_total_order` (Opt 4)

**RhoCalc** (6 categories):
- Categories: `Proc` (primary), `Name`, `Expr`, `Chan`, `Ground`, `Float`
- **Core = {Proc, Name}** — bidirectionally reachable:
  - `Proc → Name` via `edge_Proc_Name` (e.g., `POutput` has Name field)
  - `Name → Proc` via `edge_Name_Proc` (e.g., `NQuote` has Proc field)
- **Non-core = {Expr, Chan, Ground, Float}** — proven unreachable from `Proc`:
  - `rho_Proc_reach_only_Proc_Name`: Proc can only reach {Proc, Name}
  - `rho_Expr_not_core`, `rho_Chan_not_core`, `rho_Ground_not_core`, `rho_Float_not_core`
- Demonstrates SCC splitting (Opt 5): Core struct has only Proc/Name rules

## File Index

| File | Description |
|------|-------------|
| [tls-pool-equivalence.md](tls-pool-equivalence.md) | Opt 2: TLS Vec Pool Iteration Equivalence |
| [dead-rule-pruning.md](dead-rule-pruning.md) | Opt 3: Reachability-Based Dead Rule Pruning |
| [ordvar-scope-ordering.md](ordvar-scope-ordering.md) | Opt 4: OrdVar Total Order and Scope Total Preorder |
| [scc-splitting.md](scc-splitting.md) | Opt 5: Core/Full Fixpoint Equivalence via SCC Splitting |
| [rocq-artifacts.md](rocq-artifacts.md) | Build instructions, theorem catalog, hypothesis audit |

## See Also

- [PraTTaIL to Ascent Codegen Bridge](../../../prattail/docs/design/ascent-codegen-optimizations.md) — Where optimizations are applied in the pipeline
- [Rule Consolidation](../rule-consolidation/) — Opt 1: N-to-1 rule consolidation (separate proof suite)
- [Rocq Source](../../../formal/rocq/ascent_optimizations/theories/) — The `.v` proof files
