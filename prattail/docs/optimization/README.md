# WFST-Informed Ascent Optimization Pipeline

## Overview

The PraTTaIL compilation pipeline generates [Ascent](https://github.com/s-arash/ascent) Datalog programs that implement equational reasoning and rewriting for user-defined theories. Without optimization, the generated Ascent programs contain redundant rules, suboptimal evaluation orders, and unnecessary computations that increase fixpoint iteration count and compilation time.

The WFST-Informed Ascent Optimization pipeline uses data extracted from the WFST (Weighted Finite-State Transducer) prediction and recovery analysis — constructor weights, category diversity, dead-rule labels, isomorphic categories — to optimize the generated Ascent code at compile time. Additional optimizations use De Bruijn pattern analysis, structural subsumption, and runtime caching to further reduce both compilation and evaluation costs.

## Intuitions at a Glance

### Implemented Optimizations

#### Sprint 0 — Pipeline Analysis Data Export
- **Intuition**: Before you can optimize, you need data. This sprint builds the bridge that carries WFST analysis results (which rules are dead, how frequent each constructor is, how complex each category is) from the parser pipeline into the Ascent code generator.
- **What it does**: Creates the `PipelineAnalysis` struct and threads it through the macro expansion pipeline.
- **Why it matters**: Without this bridge, the Ascent codegen has no visibility into the grammar's runtime behavior. Every subsequent optimization depends on it.
- **Pipeline position**: Between WFST pipeline completion and Ascent code generation.

#### Sprint 1 — Dead-Rule DCE
- **Intuition**: Like removing unreachable code in a compiler — if a constructor can never appear in any valid parse (no token sequence can produce it), then all Ascent rules mentioning that constructor are dead weight. Removing them shrinks the generated code and reduces fixpoint iteration count.
- **What it does**: Skips dead constructors in HOL step rules, congruence rules, deconstruction arms, and explicit congruences.
- **Why it matters**: Dead rules participate in Ascent's O(N²) join but never produce new facts. Removing k dead rules from a category with n constructors saves O(k × n) useless comparisons per iteration.
- **Pipeline position**: First filter in each codegen function, checked before any rule generation.

#### Sprint 2 — Premise Cost Ordering
- **Intuition**: Like short-circuit evaluation in boolean expressions — put the cheapest checks first. A freshness check (O(1) set lookup) should come before an environment query (O(|relation|) scan), which should come before a universal quantifier (O(|collection| × body_cost)).
- **What it does**: Topologically sorts condition clauses by cost while respecting data dependencies, using a cost model: Freshness=1, EnvQuery=10, ForAll=100+body.
- **Why it matters**: Ascent evaluates body clauses left-to-right. Cheap fail-fast checks prune the intermediate tuple count during semi-naive evaluation.
- **Pipeline position**: Inside `generate_rule_clause_with_category()`, after LHS matching, before RHS construction.

#### Sprint 3 — Rule Ordering for Cache Locality
- **Intuition**: Like sorting a deck of cards by frequency before searching — put the most common constructors first. When the CPU's branch predictor encounters a `match` statement, it predicts the first arm as most likely. If the most frequent constructor IS the first arm, prediction accuracy improves.
- **What it does**: Sorts constructors within congruence and HOL step rule groups by WFST tropical weight (lower weight = more frequent = first position).
- **Why it matters**: Better branch prediction reduces pipeline stalls. For a category with 10 constructors where the top 3 account for 80% of terms, correct prediction avoids ~7 mispredictions per 10 evaluations.
- **Pipeline position**: After rule collection, before emission. Applied to congruence rule match arms and HOL step rule groups.

#### Sprint 4 — Body Clause Ordering (Congruence)
- **Intuition**: When checking if two compound terms are equal, check the argument positions that are most likely to DIFFER first. A highly diverse category (many constructors → many distinct terms) is more likely to produce a failing equality check than a low-diversity category (few constructors).
- **What it does**: Reorders `eq_cat` checks in congruence rules by descending category weight (most diverse first).
- **Why it matters**: Reduces the constant factor of Ascent's O(|cat|²) cross-product join by failing non-matching pairs faster.
- **Pipeline position**: Inside `generate_congruence_rules()`, after pool arm construction, before rule emission.

#### Sprint 5 — Ground Rewrite Pre-Stratum
- **Intuition**: Like computing 2+3=5 in a separate pass before solving algebra — ground computations (operating only on literals, producing only literals) converge in O(depth) iterations. Separating them into a pre-stratum avoids polluting the main SCC with trivially convergent rules.
- **What it does**: Classifies HOL step rules as Ground/Recursive/Dead. Ground rules go into a separate Ascent struct evaluated before the main fixpoint. Results seed the main fixpoint.
- **Why it matters**: A grammar with 20 ground rules and 30 recursive rules: the pre-stratum converges in ~5 iterations (term depth), while the main fixpoint's SCC iteration count is reduced because ground-only facts are already computed.
- **Pipeline position**: After rule classification, generates a separate Ascent struct. Runs first in `run_ascent_typed()`.

#### Sprint 6 — De Bruijn Pattern Trie (6a-6f)
- **Intuition**: Like a library catalog that groups books by topic regardless of which shelf they're on — De Bruijn encoding normalizes variable names so that α-equivalent patterns (same structure, different variable names) map to the same trie path. This reveals hidden relationships between rules.
- **What it does**: Builds a PathMap indexed by De Bruijn bytes. Computes dependency groups (union-find over shared constructors), α-equivalent pattern groups, and subsumption pairs.
- **Why it matters**: Dependency groups enable future multi-stratum splitting. Subsumption detection feeds into Sprint A (equation DCE). α-equivalent groups inform shared-matching optimizations.
- **Pipeline position**: After Ascent content generation, before file output. Analysis results feed into diagnostics and Sprint A DCE.

#### Sprint 7 — Variable Binding Selectivity
- **Intuition**: Like checking a person's ID before asking them detailed questions — if the ID check fails, you skip the questions entirely. Equational checks (variable equality) are interleaved into the clause sequence at the earliest position where both variables are bound, rather than collected at the end.
- **What it does**: Moves equational checks from a separate `equational_checks` list into the `clauses` list at the earliest valid position.
- **Why it matters**: Fail-fast: if the equational check fails (variables don't match), all subsequent destructuring clauses are skipped, reducing per-tuple processing cost.
- **Pipeline position**: Inside `PatternTerm::Var` handling in `pattern.rs`, during LHS clause generation.

#### Sprint 8 — Isomorphic WFST Detection (8a-8b)
- **Intuition**: Like recognizing that two different-looking maps describe the same road network — if two categories have identical WFST structures (same states, transitions, and action shapes, just different labels), they can share generated code via template instantiation.
- **What it does**: Computes canonical WFST structures with De Bruijn action indices. Groups categories by structural equality. Builds action maps from De Bruijn indices to concrete (category, rule_label) pairs.
- **Why it matters**: Foundation for future macro_rules! template instantiation (8c-8g). Currently provides diagnostic insight into grammar structure.
- **Pipeline position**: After WFST construction, during `build_pipeline_analysis()`. Results stored in `PipelineAnalysis.isomorphic_groups`.

#### Sprint 9 — Integration Testing
- **Intuition**: Trust but verify — comprehensive tests ensure that all optimizations preserve correctness across the full test suite.
- **What it does**: 4 PipelineAnalysis integration tests, 15 pattern/trie tests, 6 canonical WFST tests.
- **Why it matters**: Regression safety net. Ensures optimizations compose correctly.
- **Pipeline position**: N/A (test infrastructure).

#### Sprint A — N10 Subsumption Exploitation
- **Intuition**: Like a library card catalog: if you have a card for "all books by Author X" and another for "all mystery books by Author X", the second is redundant — the first already covers it. When one equation's LHS pattern matches strictly more terms than another's, the specific equation is subsumed.
- **What it does**: Builds a `HashSet<usize>` of subsumed equation indices from `detect_subsumption()` results. Skips these equations during Ascent codegen.
- **Why it matters**: Removes redundant equations from the fixpoint computation. Fewer rules = fewer iterations for semi-naive convergence.
- **Pipeline position**: Before Ascent codegen, after pattern trie analysis. Feeds `subsumed_equations` to `generate_equation_rules()`.

#### Sprint B — R1 Term Equality Cache
- **Intuition**: Like a phone book that remembers which numbers you already looked up — Ascent's fixpoint evaluation compares the same term pairs across multiple iterations. Caching these comparisons avoids repeated expensive α-equivalence checks involving `unbind2()` + recursive comparison.
- **What it does**: TLS `HashMap<(u64, u64), bool>` cache keyed by structural hash pairs. `cached_term_eq()` looks up cache on each call, delegates to moniker on miss.
- **Why it matters**: Reduces O(N² × K × d) equality checks to O(N² × d) after warmup (first iteration populates cache, subsequent iterations are O(1) lookups).
- **Pipeline position**: Runtime optimization in `Scope::term_eq()`. Cache cleared at start of each `run_ascent_typed()`.

#### Sprint C — C1 α-Equivalence Lint
- **Intuition**: Like a spell-checker that catches not just identical words but also words that are the same up to capitalization — G24 uses De Bruijn encoding to detect grammar rules that differ only in variable naming, catching duplicates that the string-based G07 lint misses.
- **What it does**: Encodes `SyntaxItemSpec` sequences to De Bruijn canonical bytes. Groups rules by byte equality. Reports groups where bytes match but string signatures differ.
- **Why it matters**: Catches subtle redundancies in grammar definitions. Also provides finer discrimination than G07: distinguishes `x==x` (same-variable reuse) from `a==b` (distinct variables).
- **Pipeline position**: In lint layer (`run_lints()`), after G07, before G08.

### Deferred Optimizations

#### 6g/6h — Multi-Stratum Ascent
- **Intuition**: Like splitting a jigsaw puzzle into independently solvable sections — if groups of equations share no constructors, they can be evaluated in separate Ascent structs, reducing each SCC's working set.
- **Pipeline position**: After dependency group analysis, before main fixpoint.
- **Status**: Deferred. Each additional `ascent!` struct adds ~5-10s compilation time. Current grammars have mostly single-rule independent groups.

#### 8c-8g — Template Instantiation
- **Intuition**: Like using a form letter where you fill in different names — isomorphic categories share identical generated code structure, differing only in type names and constructor labels. A `macro_rules!` template could generate code once and instantiate per category.
- **Pipeline position**: During code generation, after isomorphic group detection.
- **Status**: Deferred. 27% codegen reduction doesn't justify +15% maintenance burden per codegen change.

#### 9h/9i — Benchmark CI
- **Intuition**: Like a financial audit that runs every quarter — continuous benchmarking detects performance regressions before they ship.
- **Pipeline position**: CI/CD infrastructure.
- **Status**: Deferred. Infrastructure 95% ready. Activate when runtime performance needs monitoring.

---

## Architecture Diagram

```
┌────────────────────────────────────────────────────────────────────────────┐
│                         Grammar Specification                              │
│                    (language! { ... } macro input)                         │
└──────────────────────────────┬─────────────────────────────────────────────┘
                               │
                               ▼
┌────────────────────────────────────────────────────────────────────────────┐
│                      PraTTaIL WFST Pipeline                                │
│                                                                            │
│  ┌──────────┐   ┌───────────┐   ┌──────────┐   ┌─────────┐   ┌──────────┐  │
│  │ NFA/DFA  │──▶│ FIRST/    │──▶│Prediction│──▶│Recovery │──▶│Dead-Rule │  │
│  │ Build    │   │ FOLLOW    │   │ WFSTs    │   │ WFSTs   │   │Detection │  │
│  └──────────┘   └───────────┘   └──────────┘   └─────────┘   └──────────┘  │
│                                       │               │             │      │
│                                       ▼               ▼             ▼      │
│                              ┌────────────────────────────────────────┐    │
│                              │      PipelineAnalysis (Sprint 0)       │    │
│                              │  ● dead_rule_labels                    │    │
│                              │  ● constructor_weights                 │    │
│                              │  ● category_weights                    │    │
│                              │  ● isomorphic_groups (Sprint 8)        │    │
│                              └───────────────┬────────────────────────┘    │
│                                              │                             │
│                              ┌───────────────┼──────────────────────┐      │
│                              │  Lint Layer   │  (Sprint C: G24)     │      │
│                              │  G01-G10, G24,│W01-W06, R01-R07     │       │
│                              │  C01-C04, P02-│P04                   │      │
│                              └───────────────┼──────────────────────┘      │
└──────────────────────────────────────────────┼─────────────────────────────┘
                                               │
                                               ▼
┌────────────────────────────────────────────────────────────────────────────┐
│                    Ascent Code Generation (macros crate)                   │
│                                                                            │
│  ┌────────────────────┐                                                    │
│  │ Pattern Trie       │  Sprint 6: De Bruijn index, dependency groups,     │
│  │ Analysis           │  α-equiv groups, subsumption detection             │
│  └────────┬───────────┘                                                    │
│           │                                                                │
│           ▼                                                                │
│  ┌────────────────────┐                                                    │
│  │ Subsumption DCE    │  Sprint A (N10): eliminate subsumed equations      │
│  └────────┬───────────┘                                                    │
│           │                                                                │
│           ▼                                                                │
│  ┌────────────────────┐  ┌────────────────────┐  ┌────────────────────┐    │
│  │ Dead-Rule DCE      │  │ Premise Ordering   │  │ Rule Ordering      │    │
│  │ (Sprint 1)         │  │ (Sprint 2)         │  │ (Sprint 3)         │    │
│  └────────┬───────────┘  └────────┬───────────┘  └────────┬───────────┘    │
│           │                       │                        │               │
│           └───────────────┬───────┘────────────────────────┘               │
│                           ▼                                                │
│  ┌────────────────────────────────────────────┐                            │
│  │ Body Clause Ordering (Sprint 4)            │                            │
│  │ Variable Binding Selectivity (Sprint 7)    │                            │
│  └────────────────────────┬───────────────────┘                            │
│                           ▼                                                │
│  ┌────────────────────────────────────────────┐                            │
│  │ Pre-Stratum Generation (Sprint 5)          │                            │
│  │  Ground HOL rules → separate Ascent struct │                            │
│  └────────────────────────┬───────────────────┘                            │
│                           ▼                                                │
│  ┌────────────────────────────────────────────┐                            │
│  │ Main Ascent Struct Generation              │                            │
│  │  Relations + Category + Equation + Rewrite │                            │
│  └────────────────────────┬───────────────────┘                            │
└───────────────────────────┼────────────────────────────────────────────────┘
                            │
                            ▼
┌────────────────────────────────────────────────────────────────────────────┐
│                           Runtime Execution                                │
│                                                                            │
│  ┌──────────────────────┐                                                  │
│  │ clear_term_eq_cache()│  Sprint B (R1): reset before each evaluation     │
│  └──────────┬───────────┘                                                  │
│             ▼                                                              │
│  ┌──────────────────────┐   ┌──────────────────────┐                       │
│  │ Pre-Stratum Run      │──▶│ Main Fixpoint Run    │                       │
│  │ (ground rules only)  │   │ (seeded with ground  │                       │
│  │ O(depth) iterations  │   │  results)             │                      │
│  └──────────────────────┘   └──────────┬───────────┘                       │
│                                        │                                   │
│                              ┌─────────┴─────────┐                         │
│                              │ Term Equality Cache│  Sprint B: cached      │
│                              │ (TLS HashMap)      │  Scope::term_eq()      │
│                              └───────────────────┘                         │
└────────────────────────────────────────────────────────────────────────────┘
```

## Decision Matrix

| ID | Optimization | Status | Sprint | Tier | Activation Condition |
|----|-------------|--------|--------|------|---------------------|
| S0 | Pipeline Analysis Export | Implemented | 0 | — | Always active |
| S1 | Dead-Rule DCE | Implemented | 1 | — | When `PipelineAnalysis` available |
| S2 | Premise Cost Ordering | Implemented | 2 | — | Always active (≥2 conditions) |
| S3 | Rule Ordering (Cache Locality) | Implemented | 3 | — | When constructor_weights available |
| S4 | Body Clause Ordering | Implemented | 4 | — | When category_weights available |
| S5 | Ground Rewrite Pre-Stratum | Implemented | 5 | — | When ground HOL step rules exist |
| S6a-f | De Bruijn Pattern Trie | Implemented | 6 | — | When equations/rewrites exist |
| S7 | Variable Binding Selectivity | Implemented | 7 | — | Always active (duplicate vars) |
| S8a-b | Isomorphic WFST Detection | Implemented | 8 | — | Always active |
| S9a-g | Integration Testing | Implemented | 9 | — | Test infrastructure |
| N10 | Subsumption Exploitation | Implemented | A | A | When equation subsumption detected |
| R1 | Term Equality Cache | Implemented | B | A | Always active (runtime) |
| C1 | α-Equivalence Lint (G24) | Implemented | C | A | Always active (lint layer) |
| 6g/6h | Multi-Stratum Ascent | Deferred | — | D | ≥2 independent groups with ≥5 rules each |
| 8c-8g | Template Instantiation | Deferred | — | D | 5+ isomorphic category sets |
| 9h/9i | Benchmark CI | Deferred | — | D | When runtime monitoring needed |
| R2 | Lazy binder construction | Rejected | — | — | Proven unsound (Sprint 5 analysis) |

## Optimization Pipeline Flow

The optimizations compose in a specific order during Ascent code generation:

```
Grammar Definition
       │
       ▼
┌──────────────┐     ┌──────────────┐
│ WFST Pipeline│────▶│ Pipeline     │
│ (NFA → DFA → │     │ Analysis     │
│  WFST)       │     │ Export (S0)  │
└──────────────┘     └──────┬───────┘
                            │
       ┌────────────────────┼────────────────────┐
       ▼                    ▼                    ▼
  ┌─────────┐      ┌──────────────┐     ┌────────────┐
  │ Dead    │      │ Pattern Trie │     │ Lint Layer │
  │ Labels  │      │ (S6)         │     │ (S9, C1)   │
  └────┬────┘      └──────┬───────┘     └────────────┘
       │                  │
       │           ┌──────┴───────┐
       │           ▼              ▼
       │    ┌────────────┐  ┌──────────┐
       │    │ Subsumption│  │ α-equiv  │
       │    │ DCE (N10)  │  │ Groups   │
       │    └─────┬──────┘  └──────────┘
       │          │
       ▼          ▼
  ┌──────────────────────────────┐
  │  Equation Rule Generation    │
  │  ● Skip dead (S1)            │
  │  ● Skip subsumed (N10)       │
  │  ● Cost-order premises (S2)  │
  │  ● Interleave eq checks(S7)  │
  └─────────────┬────────────────┘
                │
  ┌─────────────┴────────────────┐
  │  Rewrite Rule Generation     │
  │  ● Skip dead (S1)            │
  │  ● Weight-sort rules (S3)    │
  │  ● Cost-order premises (S2)  │
  │  ● Interleave eq checks(S7)  │
  └─────────────┬────────────────┘
                │
  ┌─────────────┴────────────────┐
  │  Congruence Rule Generation  │
  │  ● Skip dead (S1)            │
  │  ● Weight-sort arms (S3)     │
  │  ● Diversity-order eq (S4)   │
  └─────────────┬────────────────┘
                │
  ┌─────────────┴────────────────┐
  │  Stratum Splitting (S5)      │
  │  ● Ground → pre-stratum      │
  │  ● Recursive → main          │
  └─────────────┬────────────────┘
                │
                ▼
  ┌──────────────────────────────┐
  │  Generated Ascent Code       │
  │  (pre-stratum + main struct) │
  └──────────────┬───────────────┘
                 │
                 ▼
  ┌──────────────────────────────┐
  │  Runtime Execution           │
  │  ● Term eq cache (R1)        │
  │  ● Pre-stratum → main        │
  └──────────────────────────────┘
```

## Mathematical Foundations

### α-Equivalence and De Bruijn Indices

Two terms are **α-equivalent** (written t₁ ≡α t₂) if they differ only in the names of bound variables:

    λx. x + y  ≡α  λz. z + y

**De Bruijn encoding** replaces named variables with positional indices. The first occurrence of a variable in encounter order gets tag `NewVar` (0xC0), subsequent occurrences get `VarRef(slot)` (0x80 | slot). This produces a **canonical** byte sequence:

    encode(t₁) = encode(t₂)  ⟺  t₁ ≡α t₂

### Tropical Semiring Weights

Constructor weights use the **tropical semiring** ⟨ℝ ∪ {∞}, min, +, ∞, 0⟩ where:
- ⊕ = min (best path wins)
- ⊗ = + (costs accumulate along paths)
- 0̄ = ∞ (identity for min)
- 1̄ = 0 (identity for +)

Lower weight = more frequent constructor in WFST dispatch.

### Subsumption Ordering

Pattern P **subsumes** pattern Q (written P ⊒ Q) if every term matching Q also matches P. In De Bruijn encoding, this is checked structurally:

- A single variable subsumes everything: `x ⊒ f(a, b)`
- Matching constructors with a more general argument: `f(x, y) ⊒ f(g(a), y)`

For equations (symmetric rules), P ⊒ Q implies the general equation already produces all `eq_cat` facts the subsumed equation would, making it safe to eliminate.

### Fixpoint Convergence

Ascent uses **semi-naive evaluation**: each iteration only considers tuples derived in the previous iteration (Δ-facts). The fixpoint converges when no new tuples are produced.

- Ground pre-stratum: O(d) iterations where d = term nesting depth
- Main fixpoint: O(N × K) where N = term count, K = max rewrite chain length
- Term equality cache: amortized O(1) per comparison after first iteration

## Cross-References

- [Sprint A: N10 Subsumption Exploitation](n10-subsumption.md)
- [Sprint B: R1 Term Equality Cache](r1-term-equality-cache.md)
- [Sprint C: C1 α-Equivalence Lint](c1-alpha-equiv-lint.md)
- [Completed Sprints (0-9, A-C)](completed-sprints.md)
- [Deferred and Rejected Items](deferred-and-rejected.md)
