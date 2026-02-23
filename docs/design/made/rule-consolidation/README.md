# Ascent Rule Consolidation Proofs

## Executive Summary

Rule consolidation (Opt 1) replaces N per-constructor Ascent Datalog rules with 1 consolidated rule containing an inline `match` expression. This reduces the Ascent rule count by ~55% (347 → 157 rules across all languages) and dramatically improves compilation time, since each Ascent rule expands to ~120 lines of Rust code during proc-macro compilation.

Six consolidation areas have been formally verified in Rocq (Coq 9.1), covering all pattern-matching consolidation transforms applied by the MeTTaIL code generator:

| Area | Description                 | Core Theorem                      | Rocq File               | Lines |
|------|-----------------------------|-----------------------------------|-------------------------|-------|
| 1    | Subterm Extraction          | R1: `for_match_equiv`             | `RuleConsolidation.v`   | 400   |
| 2    | Auto-Variant Congruence     | R1: `for_match_equiv`             | `RuleConsolidation.v`   | 400   |
| 3    | Equation Congruence         | R3: `pair_match_equiv`            | `RuleConsolidation.v`   | 400   |
| 4    | Explicit Rewrite Congruence | V4: `variant_index_extract_equiv` | `VariantIndexRebuild.v` | 266   |
| 5    | Fold Triggers               | R2: `if_match_equiv`              | `RuleConsolidation.v`   | 400   |
| 6    | Fold Identities             | R2: `if_match_equiv`              | `RuleConsolidation.v`   | 400   |

**Total: 5 Rocq files, 1,469 lines, zero `Admitted`.**

## Context

The MeTTaIL compilation pipeline transforms a `language!` macro invocation into two artifacts:

1. A **PraTTaIL parser** (Pratt + recursive descent) for syntactic analysis
2. An **Ascent Datalog program** for semantic analysis (rewriting, equation solving, fold evaluation)

The Ascent program generates rules from the language definition. Without consolidation, the number of rules grows as O(C^2 * N) where C is the category count and N is the constructor count. Rule consolidation reduces this to O(C^2) by replacing N per-constructor `if let` rules with 1 consolidated `match` rule per (source, target) category pair.

The semantic equivalence argument: a Datalog rule fires independently for each binding of its variables. An inline `match` over all constructors in a single `for` clause produces exactly the same set of bindings as N separate `if let` rules would — the union of all constructor matches.

## Proof Architecture

The 5 Rocq files form a dependency DAG:

```
                Prelude.v (183)
               /         \
              v           v
DisjointPatterns.v   RuleConsolidation.v
     (192)                (400)
              \         /     \
               v       v       v
         AreaProofs.v    VariantIndexRebuild.v
            (428)              (266)
```

**Shared infrastructure** (`Prelude.v`, 183 lines):
- Multiset equivalence via `Permutation` (notation `l1 ≡ₘ l2`)
- `flat_map` lemmas: `flat_map_nil`, `flat_map_cons`, `flat_map_app`, `flat_map_singleton`
- Key workhorse: `flat_map_all_nil` (all arms produce `[]` → result is `[]`) and `flat_map_single_hit` (exactly one arm produces non-`[]` → result is that arm's output)
- Conditional extraction (`cond_extract`) modeling `if classify(t) = Some k then extract(k, t) else []`
- Decidable equality for option types (`option_eqb`, `option_eqb_spec`)

**Pattern matching model** (`DisjointPatterns.v`, 192 lines):
- Abstract interface: `classify`, `extract`, `all_kinds`, `eqb_K`
- D1: `classify_unique` — at most one kind matches (determinism of functions)
- D2: `match_extract_some` — `match_extract(t) = extract(k, t)` when `classify(t) = Some k`
- D3: `match_extract_none` — `match_extract(t) = []` when `classify(t) = None`
- `per_kind_extract` with hit/miss/none helper lemmas
- `original_rules` definition: `flat_map per_kind_extract all_kinds`

## Concrete Instantiation

All area proofs are instantiated for the Calculator language's `IntKind` type with 8 constructors:

```
Inductive IntKind := KAdd | KSub | KNeg | KPow | KFact | KTern | KCustomOp | KNumLit.
```

Infrastructure: `eqb_IntKind_spec` (decidable equality), `all_IntKinds_complete` (exhaustive enumeration), `all_IntKinds_nodup` (no duplicates). These three properties hold for any Rust `enum` type, making the proofs applicable to all MeTTaIL language definitions.

## Results

| Language   | Before  | After   | Reduction |
|------------|---------|---------|-----------|
| Calculator | 138     | 61      | 56%       |
| Rho Calc   | 116     | 52      | 55%       |
| Ambient    | 84      | 35      | 58%       |
| Lambda     | 9       | 9       | 0%        |
| **Total**  | **347** | **157** | **55%**   |

Lambda has only 1 category (Term) so there was nothing to consolidate.

## File Index

| File                                             | Description                                                          |
|--------------------------------------------------|----------------------------------------------------------------------|
| [overview.md](overview.md)                       | Problem statement, technique, results, source file inventory         |
| [consolidation-areas.md](consolidation-areas.md) | Detailed before/after for each of the 6 consolidation areas          |
| [formal-proofs.md](formal-proofs.md)             | Complete formal proofs: definitions, theorems, and area applications |
| [rocq-artifacts.md](rocq-artifacts.md)           | Build instructions, theorem catalog, hypothesis audit                |
| [codegen-dry.md](codegen-dry.md)                 | DRY improvements to the codegen source code                          |

## See Also

- [Ascent Runtime Optimizations](../ascent-optimizations/) — Opts 2-5: TLS pooling, dead rule pruning, ordering, SCC splitting
- [PraTTaIL to Ascent Codegen Bridge](../../../../prattail/docs/design/ascent-codegen-optimizations.md) — Where optimizations are applied in the pipeline
- [Rocq Source](../../../../formal/rocq/rule_consolidation/theories/) — The `.v` proof files
