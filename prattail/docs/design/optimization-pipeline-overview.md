# Optimization Pipeline Overview

| Field   | Value                     |
|---------|---------------------------|
| Date    | 2026-03-09                |
| Status  | Reference documentation   |

---

## Table of Contents

- [1 Optimization Layer Taxonomy](#1-optimization-layer-taxonomy)
- [2 Dependency DAG](#2-dependency-dag)
- [3 Cost-Benefit Gate Activation Table](#3-cost-benefit-gate-activation-table)
- [4 Before/After Code Snippets](#4-beforeafter-code-snippets)
- [5 Interaction with Analysis Results](#5-interaction-with-analysis-results)

---

## 1 Optimization Layer Taxonomy

PraTTaIL's optimization system comprises **7 layers** organized by target backend,
totaling **50 optimization variants** registered in the `Optimization` enum
(`prattail/src/cost_benefit.rs`). Each variant has a cost-benefit gate, an
applicability predicate, and a corresponding field in `OptimizationGates` that
controls whether the optimization is emitted during code generation.

### Layer A-RT: Ascent Runtime (6 optimizations)

These target the **runtime behavior** of generated Ascent Datalog programs,
reducing allocation pressure, iteration count, and memory consumption during
fixpoint evaluation.

| ID     | Name                    | Target                                  | Key Files                                   |
|--------|-------------------------|-----------------------------------------|---------------------------------------------|
| ART01  | Hash-Consing            | Replace `Box<T>` with `Rc<T>` + interning table | `macros/src/gen/runtime/language.rs`, `runtime/src/hash_consing.rs` |
| ART02  | Incremental Delta       | Semi-naive delta guards on relations     | `macros/src/logic/rules.rs`, `macros/src/logic/equations.rs` |
| ART03  | Relation Indexing       | `#[index]` annotations on bound columns  | `macros/src/logic/relations.rs`             |
| ART04  | Congruence Bloom        | Bloom filter pre-check before congruence | `macros/src/logic/bloom_filter.rs`, `macros/src/logic/congruence.rs` |
| ART05  | Depth Bound             | Term-depth convergence bound             | `macros/src/gen/term_ops/depth.rs`          |
| ART06  | Demand-Driven           | Skip eq/rw rules for non-demanded cats   | `macros/src/logic/common.rs`, `macros/src/logic/equations.rs` |

**ART06 detail:** The demand filtering computes the set of categories referenced by
at least one equation, rewrite, or logic rule. Categories not in this set have
their reflexivity, congruence, and rewrite rules entirely skipped during codegen.
This is an always-on analysis (no feature gate) that eliminates dead rule
generation at compile time.

### Layer B-CG: Ascent Codegen (6 optimizations)

These transform the **structure** of generated Ascent rules, reordering clauses,
fusing rules, and stratifying evaluation for faster fixpoint convergence.

| ID     | Name                    | Target                                  | Key Files                                   |
|--------|-------------------------|-----------------------------------------|---------------------------------------------|
| BCG01  | Join Ordering           | Reorder body clauses by selectivity      | `macros/src/logic/common.rs`                |
| BCG02  | Rule Fusion             | Fuse deconstruction-rewrite chains       | `macros/src/logic/fusion.rs`                |
| BCG03  | Eq-Congruence Prune     | Skip congruence for non-participating constructors | `macros/src/logic/equations.rs`  |
| BCG04  | Ground Short-Circuit    | Seed ground rewrites at initialization   | `macros/src/logic/rules.rs`                 |
| BCG05  | Normalize-Dedup         | Hash guard before normalize() calls      | `macros/src/logic/categories.rs`, `macros/src/logic/rules.rs` |
| BCG06  | Eq-Strata               | SCC-based stratification of equation rules | `macros/src/logic/equations.rs`            |

**BCG02 detail:** Rule fusion detects chains where a deconstruction rule extracts
subterms that feed a rewrite rule. The fused rule directly matches the parent
constructor and applies the rewrite, eliminating the intermediate `cat(sub)`
tuple. Safety conditions:
1. The intermediate relation is consumed only by the candidate rewrite rule
2. The rewrite rule has no congruence premises
3. The rewrite LHS is a simple constructor application

**BCG06 detail:** Equation stratification performs SCC analysis on the dependency
graph of equation rules (reflexivity, congruence, user-defined). Rules are sorted
by stratum index so that equations with fewer inter-stratum dependencies evaluate
first, enabling faster convergence.

### Layer C-AP: Codegen Antipatterns (5 detections)

These are **detection-only** -- they identify common performance antipatterns in
user-defined logic blocks, grammar constructors, and rewrite rules, emitting
lint warnings (A01-A10 in `lint.rs`) without performing transformations.

| ID     | Detection               | Lint ID | Description                              |
|--------|-------------------------|---------|------------------------------------------|
| CAP01  | Fixpoint non-convergence| A01     | Depth-increasing rules without bound     |
| CAP02  | Redundant congruence    | A02     | Congruence on category with 1 constructor|
| CAP03  | Category mismatch       | A03     | eq/rw LHS category != rule category      |
| CAP04  | Large equiv class       | A04     | Equivalence class exceeding threshold    |
| CAP05  | Self-referential eq     | A05     | Equation `f(X) = f(X)` (tautology)      |

### Layer A-L: Lexer Codegen (6 optimizations)

These optimize the generated DFA-based lexer for faster token recognition.

| ID     | Name                    | Target                                  | Key Files                                   |
|--------|-------------------------|-----------------------------------------|---------------------------------------------|
| AL01   | Comb Repacking          | Multi-row DFA transition table packing   | `prattail/src/automata/codegen.rs`          |
| AL02   | Hybrid Lexer            | Hot states direct-coded, cold compressed | `prattail/src/lexer.rs`                     |
| AL03   | SIMD Whitespace         | `std::simd` 16-byte whitespace scanning  | `prattail/src/lexer.rs` (feature: `simd-whitespace`) |
| AL04   | Keyword MPH             | Minimal perfect hashing for keywords     | `prattail/src/automata/mph.rs`              |
| AL05   | Multi-Byte Chain        | Collapse single-path DFA chains          | `prattail/src/automata/codegen.rs`          |
| AL06   | Accept Bitmap Widen     | Widen accept state bitmap to u64/u128    | `prattail/src/automata/codegen.rs`          |

### Layer B-P: Parser Codegen (5 optimizations)

These optimize the generated Pratt + recursive-descent parser.

| ID     | Name                    | Target                                  | Key Files                                   |
|--------|-------------------------|-----------------------------------------|---------------------------------------------|
| BP01   | BP Compaction           | Range-encode binding power tables        | `prattail/src/binding_power.rs`             |
| BP02   | Tail-Call Elim          | Tail-call in recursive descent           | `prattail/src/trampoline.rs`                |
| BP03   | BP Table Lookup         | Token peek cache for BP lookups          | `prattail/src/pratt.rs`                     |
| BP04   | Trivial Inline          | Inline trivial RD handlers into trampoline | `prattail/src/pipeline.rs`                |
| BP05   | BP Range Loop           | Specialized Pratt loop for fixed ranges  | `prattail/src/pratt.rs`                     |

### Layer C-D: Dispatch Codegen (5 optimizations)

These optimize the parse dispatch mechanism powered by PathMap decision trees.

| ID     | Name                    | Target                                  | Key Files                                   |
|--------|-------------------------|-----------------------------------------|---------------------------------------------|
| CD01   | Frequency Ordering      | WFST-weight arm reordering               | `prattail/src/dispatch.rs`                  |
| CD02   | Segment Merging         | Merge safe NT boundary segments          | `prattail/src/decision_tree.rs`             |
| CD03   | Computed Goto           | Function pointer table dispatch          | `prattail/src/decision_tree.rs`             |
| CD04   | Jump Threading          | Thread through DT branch chains          | `prattail/src/decision_tree.rs`             |
| CD05   | Prefix CSE              | Common subexpression for shared NT parses| `prattail/src/decision_tree.rs`             |

### Layer D-B: Build / Pipeline (4 optimizations)

These optimize the compilation pipeline itself, reducing build times and
eliminating redundant analysis.

| ID     | Name                    | Target                                  | Key Files                                   |
|--------|-------------------------|-----------------------------------------|---------------------------------------------|
| DB01   | Incremental FF          | Dirty-flag FIRST/FOLLOW computation      | `prattail/src/prediction.rs`                |
| DB02   | Lazy Analysis           | Skip analyses for small grammars         | `prattail/src/pipeline.rs`                  |
| DB03   | Parallel Analysis       | `std::thread::scope` for analyses        | `prattail/src/pipeline.rs`                  |
| DB04   | Cached Lints            | Hash-based lint cache across builds      | `prattail/src/lint.rs`                      |

---

## 2 Dependency DAG

Optimizations form a dependency graph where some optimizations require analysis
results from others. The arrows indicate "B requires output from A."

```text
  ┌───────────────────────────────────────────────────────────────────┐
  │                    Analysis Prerequisites                          │
  │                                                                    │
  │  FIRST/FOLLOW ──────────┬──────────── PredictionWfst              │
  │    (Phase 2)            │               (Phase 3)                  │
  │                         │                   │                      │
  │                         │                   ├──── DecisionTree     │
  │                         │                   │      (Phase 4)       │
  │                         │                   │                      │
  │                         │                   ├──── GrammarProfile   │
  │                         │                   │      (D1)            │
  │                         │                   │                      │
  │                         │                   └──── OptimizationGates│
  │                         │                           (A3)           │
  │                         │                                          │
  │  DB01 ──── accelerates ─┘                                         │
  └───────────────────────────────────────────────────────────────────┘

  ┌───────────────────────────────────────────────────────────────────┐
  │              Optimization Dependencies                             │
  │                                                                    │
  │  GrammarProfile ──→ gates ALL optimizations via predicates         │
  │                                                                    │
  │  A4 (EnhancedDCE) ──→ dead rule labels ──→ DT exclusion           │
  │                                              │                     │
  │                                              └──→ ART06 demand     │
  │                                                    filtering       │
  │                                                                    │
  │  A5 (AmbiguityTargeting) ──→ B1 (MultiTokenLookahead)             │
  │                                                                    │
  │  B3 (WfstMinimization) ──→ prediction WFST state count reduction  │
  │                                 │                                  │
  │                                 └──→ CD01 (FrequencyOrdering)      │
  │                                                                    │
  │  G1 (BacktrackingElimination) ──→ DT DisjointSuffix strategy      │
  │                                                                    │
  │  H1 (ContextDisambiguation) ──→ NFA try-all candidate narrowing   │
  │                                                                    │
  │  G25 (WpdsReachability) ──→ INT-01 weight refinement              │
  │                             ──→ INT-02 dead rule recording         │
  │                             ──→ INT-03 NFA spillover reduction     │
  │                                                                    │
  │  BCG06 (EqStrata) ──→ BCG03 (EqCongruencePrune) ordering          │
  │                                                                    │
  │  ART06 (DemandDriven) ──→ BCG03 scope (which cats to prune)       │
  │                                                                    │
  │  DB02 (LazyAnalysis) ──→ gates DT construction, WPDS, math phase  │
  │                                                                    │
  │  DB03 (ParallelAnalysis) ──→ gates thread::scope execution         │
  │                                                                    │
  │  DB04 (CachedLints) ──→ gates lint hash comparison                 │
  └───────────────────────────────────────────────────────────────────┘
```

**Execution order within the pipeline:**

```text
Phase 2:  DB01 ──→ FIRST/FOLLOW computation
Phase 3:  B3 ──→ WFST cascade
Phase 3+: A5, B1, H1 ──→ WFST enrichment
Phase 4:  G1 ──→ DT suffix disjointness
Phase 4+: A4 ──→ dead rule collection (uses DT)
Phase 5:  G25 ──→ WPDS analysis
Phase 5:  DB03 ──→ parallel math analyses
Phase 6:  DB04 ──→ lint caching
Phase 7:  BP04, AL02, CD01, CD03 ──→ codegen emission
Macros:   ART01-06, BCG01-06 ──→ Ascent rule generation
```

---

## 3 Cost-Benefit Gate Activation Table

Each optimization has a `GrammarProfile` predicate that determines applicability.
The score is `ProductWeight<speedup, compile_cost>` (lexicographic; lower = better).

### Always Applicable

| ID    | Optimization            | Speedup | Cost | Reason                           |
|-------|-------------------------|---------|------|----------------------------------|
| B2    | AdaptiveRecovery        | 0.30    | 0.10 | Zero happy-path overhead         |
| G1    | BacktrackingElimination | 0.20    | 0.10 | Static FIRST set analysis        |
| BP04  | TrivialInline           | 0.30    | 0.05 | Trivial prefix handlers          |
| AL06  | AcceptBitmapWiden       | 0.15    | 0.02 | Bitmap widening                  |
| CD01  | FrequencyOrdering       | 0.35    | 0.10 | WFST frequency arm reordering    |
| AL01  | CombRepacking           | 0.40    | 0.10 | DFA table repacking              |
| AL03  | SimdWhitespace          | 0.20    | 0.30 | Feature-gated at codegen         |

### Predicate-Gated

| ID     | Optimization            | Speedup | Cost | Predicate                                           |
|--------|-------------------------|---------|------|-----------------------------------------------------|
| A1     | LeftFactoring           | -ln(r)  | 0.1c | `shared_prefix_ratio > 0.3`                         |
| A2     | HotColdSplitting        | -ln(f)  | 0.05 | `cold_fraction > 0.4`                               |
| A4     | EnhancedDCE             | 0.50    | 0.20 | `rule_count > 5`                                    |
| A5     | AmbiguityTargeting      | -ln(a)  | 0.10 | `ambiguous_fraction > 0.1`                           |
| B1     | MultiTokenLookahead     | -ln(a)  | 0.5n | `ambiguous_fraction > 0.1 && ambiguous_count < 10`  |
| B3     | WfstMinimization        | -ln(s)  | 0.15 | `total_wfst_states > 4`                             |
| F1     | SpilloverPruning        | 0.20    | 0.01 | `has_beam_width && nfa_spillover > 0`                |
| F2     | EarlyTermination        | 0.10    | 0.01 | `nfa_spillover == 0 && ambiguous_count > 0`          |
| F3     | LazySpillover           | 0.30    | 0.30 | `nfa_spillover > 0`                                  |
| H1     | ContextDisambiguation   | -0.8ln  | 0.20 | `nfa_spillover > 0 && ambiguous_fraction > 0.05`     |
| G25    | WpdsReachability        | 0.40    | 0.30 | `category_count >= 2`                                |
| ART01  | HashConsing             | 0.15    | 0.50 | `rule_count > 10`                                    |
| ART02  | IncrementalDelta        | 0.30    | 0.35 | `rule_count > 5`                                     |
| ART03  | RelationIndexing        | 0.30    | 0.05 | `rule_count > 3`                                     |
| ART04  | CongruenceBloom         | 0.35    | 0.15 | `rule_count > 5`                                     |
| ART05  | DepthBound              | 0.40    | 0.10 | `rule_count > 2`                                     |
| ART06  | DemandDriven            | 0.50    | 0.10 | `category_count >= 2`                                |
| BCG01  | JoinOrdering            | 0.40    | 0.15 | `rule_count > 5`                                     |
| BCG02  | RuleFusion              | 0.40    | 0.40 | `rule_count > 5`                                     |
| BCG03  | EqCongruencePrune       | 0.35    | 0.15 | `rule_count > 3`                                     |
| BCG04  | GroundShortCircuit      | 0.40    | 0.05 | `rule_count > 2`                                     |
| BCG05  | NormalizeDedup          | 0.45    | 0.10 | `rule_count > 3`                                     |
| BCG06  | EqStrata                | 0.30    | 0.40 | `category_count >= 2`                                |
| AL02   | HybridLexer             | 0.30    | 0.20 | `total_wfst_states > 30`                             |
| AL04   | KeywordMph              | 0.20    | 0.30 | `rule_count > 15`                                    |
| AL05   | MultiByteChain          | 0.25    | 0.35 | `rule_count > 10`                                    |
| BP01   | BpCompaction            | 0.25    | 0.05 | `category_count >= 1`                                |
| BP02   | TailCallElim            | 0.40    | 0.20 | `category_count >= 2`                                |
| BP03   | BpTableLookup           | 0.30    | 0.15 | `rule_count > 8`                                     |
| BP05   | BpRangeLoop             | 0.45    | 0.15 | `rule_count > 5`                                     |
| CD02   | SegmentMerging          | 0.30    | 0.35 | `avg_trie_depth > 3.0`                               |
| CD03   | ComputedGoto            | 0.25    | 0.15 | `rule_count > 20`                                    |
| CD04   | JumpThreading           | 0.35    | 0.25 | `avg_trie_depth > 2.0`                               |
| CD05   | PrefixCse               | 0.15    | 0.45 | `shared_prefix_ratio > 0.2`                          |
| DB01   | IncrementalFF           | 0.40    | 0.20 | `category_count >= 3`                                |
| DB02   | LazyAnalysis            | 0.50    | 0.02 | `category_count < 3`                                 |
| DB03   | ParallelAnalysis        | 0.30    | 0.30 | `category_count >= 3`                                |
| DB04   | CachedLints             | 0.45    | 0.20 | `rule_count > 10`                                    |

Where `-ln(r)` means `-ln(shared_prefix_ratio)`, `-ln(f)` = `-ln(cold_fraction)`,
`-ln(a)` = `-ln(ambiguous_fraction)`, `-ln(s)` = `-ln(total_wfst_states)`,
`c` = `category_count`, `n` = `ambiguous_count`.

---

## 4 Before/After Code Snippets

### BCG02: Rule Fusion

**Before** (two separate Ascent rules):

```text
// Deconstruction: extract subterms from PPar constructor
cat_proc(sub) <-- cat_proc(t), for sub in all_subterms_proc_proc(t);

// Rewrite: pattern-match PDrop constructor and produce rewrite
rw_proc(s_orig, result) <--
    eq_proc(s_orig, s),
    if let Proc::PDrop(p) = s,
    let result = Proc::PNil;
```

**After** (fused rule, additive alongside originals):

```text
// Fused: directly match PDrop inside PPar deconstruction
rw_proc(s_orig, result) <--
    cat_proc(parent),
    if let Proc::PPar(left, right) = parent,
    eq_proc(s_orig, left),     // or right
    if let Proc::PDrop(p) = left,
    let result = Proc::PNil;
```

The fused rule fires in the **same iteration** as the deconstruction, eliminating
the intermediate `cat_proc(sub)` insertion for the matched subterm.

### ART06: Demand Filtering

**Before** (all categories get reflexivity + congruence):

```text
// Generated for ALL categories, even unused ones:
eq_str(t, t) <-- cat_str(t);                          // reflexivity
eq_str(s, t) <-- eq_str(a, b), ..., let s = ..., t = ...; // congruence
```

**After** (only demanded categories):

```text
// Str category has NO equations/rewrites referencing it:
// eq_str reflexivity SKIPPED
// eq_str congruence SKIPPED

// Proc category IS demanded (has rewrites):
eq_proc(t, t) <-- cat_proc(t);                        // generated
```

### CD03: Computed Goto Dispatch

**Before** (match arms with sequential comparisons):

```rust
match peek_token {
    Token::KwNew  => parse_new(tokens, pos),
    Token::KwFor  => parse_for(tokens, pos),
    Token::KwIf   => parse_if(tokens, pos),
    Token::Ident  => parse_var(tokens, pos),
    // ... 20+ arms
    _ => Err(ParseError),
}
```

**After** (function pointer table indexed by token ID):

```rust
static DISPATCH_TABLE: [fn(&[Token], usize) -> Result<...>; 128] = {
    let mut table = [parse_error as fn(_, _) -> _; 128];
    table[TOKEN_ID_KW_NEW]  = parse_new;
    table[TOKEN_ID_KW_FOR]  = parse_for;
    table[TOKEN_ID_KW_IF]   = parse_if;
    table[TOKEN_ID_IDENT]   = parse_var;
    // ...
    table
};

// Dispatch: O(1) indirect call
(DISPATCH_TABLE[token_to_id(peek_token)])(tokens, pos)
```

### BCG05: Normalize-Dedup

**Before** (unconditional normalize call):

```text
rw_proc(s_orig, result) <--
    eq_proc(s_orig, s),
    if let Proc::PPar(a, b) = s,
    let result = normalize_proc(Proc::PPar(a, b));
```

**After** (hash guard before normalize):

```text
rw_proc(s_orig, result) <--
    eq_proc(s_orig, s),
    if let Proc::PPar(a, b) = s,
    let hash_before = structural_hash(&Proc::PPar(a, b)),
    let result = normalize_proc(Proc::PPar(a, b)),
    if structural_hash(&result) != hash_before;  // skip if unchanged
```

### G1: Backtracking Elimination (DT DisjointSuffix)

**Before** (NFA try-all with save/restore):

```rust
// Token::KwIf is ambiguous: could be IfThen or IfThenElse
let save = pos;
if let Ok(r) = parse_if_then(tokens, pos) { return Ok(r); }
pos = save;
if let Ok(r) = parse_if_then_else(tokens, pos) { return Ok(r); }
pos = save;
return Err(ParseError);
```

**After** (disjoint suffix via DT analysis):

```rust
// DT reveals: after "if <Expr> then <Expr>", look at next token:
//   "else" -> IfThenElse (COMMIT)
//   _      -> IfThen (COMMIT)
let r = parse_expr(tokens, pos)?;  // shared prefix: "if <Expr> then <Expr>"
match tokens[pos] {
    Token::KwElse => { pos += 1; let e = parse_expr(tokens, pos)?; IfThenElse(r, e) }
    _ => IfThen(r)
}
```

---

## 5 Interaction with Analysis Results

The optimization pipeline is deeply integrated with the analysis modules described
in the [Analysis Pipeline Overview](analysis-pipeline-overview.md). This section
describes how analysis results feed into optimization decisions.

### WFST Analysis → Optimization Gates

The `GrammarProfile` struct is the primary bridge between analysis and optimization.
It is computed from WFST analysis and PathMap decision tree metrics:

```text
  PredictionWfst ──→ ambiguous_fraction, cold_fraction, total_wfst_states
  PathMap DTs    ──→ avg_trie_depth, ambiguity_score, deterministic_ratio
  NFA spillover  ──→ shared_prefix_ratio, nfa_spillover_categories
```

The pipeline calls `build_grammar_profile()` after WFST construction and
updates it again after decision tree construction (to incorporate DT metrics).
Then `evaluate_optimizations()` scores all 50 candidates against the profile
and `OptimizationGates::from_env_or_recommendations()` materializes boolean
flags.

### Decision Tree → Dispatch Optimizations

The PathMap decision tree determines the dispatch strategy per token:

| Strategy         | Used By       | Description                                   |
|------------------|---------------|-----------------------------------------------|
| `Singleton`      | CD01, BP04    | One rule per token -- commit without backtrack |
| `DisjointSuffix` | G1, CD05      | Shared prefix with disjoint continuations      |
| `NfaTryAll`      | H1, F1-F3    | Multiple overlapping candidates                |
| `NotPresent`     | A4 (DCE)      | Token not reachable -- dead code               |

CD01 (FrequencyOrdering) uses WFST weights from prediction WFSTs to sort
`Ambiguous` candidates by frequency, ensuring hot-path arms appear first in
generated match expressions.

CD02 (SegmentMerging) examines nonterminal boundaries in the DT where
multiple rules share the same NT parse but diverge afterward. If the
continuations are disjoint, the segments can be merged, eliminating
redundant NT parses.

### WPDS Analysis → Dead Rule Refinement

G25 (WPDS Reachability) produces three downstream effects:

1. **INT-01**: Prediction WFST weight refinement -- for rules with equal WFST
   weights sharing a dispatch token, WPDS poststar weights break ties (lower
   WPDS weight translates to lower WFST weight).

2. **INT-02**: Dead rule recording -- WPDS-unreachable rules are recorded
   for codegen suppression. The PathMap trie structure is immutable, but
   codegen can skip `Ambiguous` candidates that are WPDS-dead.

3. **INT-03**: NFA spillover reduction -- WPDS-dead rules are removed from
   NFA spillover groups. If all ambiguous groups in a category become
   singletons, the category is removed from `nfa_spillover_categories`.

### Mathematical Analyses → Lint-Driven Optimization

Several analysis modules produce diagnostics that inform optimization decisions
at the grammar design level (not automatic code transformation):

| Analysis         | Lint  | Optimization Guidance                             |
|------------------|-------|---------------------------------------------------|
| TRS confluence   | T01   | Non-joinable critical pairs indicate rewrite bugs  |
| TRS termination  | T03   | Non-terminating cycles suggest depth bound need   |
| VPA analysis     | V01   | Determinizable VPA suggests backtrack elimination  |
| Safety verify    | S01   | Safety violations indicate unreachable paths      |
| CEGAR refinement | S03   | Refinement steps suggest precision needs          |
| Petri deadlock   | N01   | Deadlock risk in concurrent grammar patterns      |
| KAT check        | K01   | Hoare triple failures indicate semantic bugs       |

The cost-benefit framework includes gates for these analyses:
- `TrsConfluenceCheck`: `rule_count > 3`
- `VpaInclusionCheck`: `category_count >= 1`
- `SafetyVerification`: `category_count >= 2`
- `CegarRefinement`: `category_count >= 2`
- `PetriDeadlockCheck`: `rule_count > 5`

### Ascent Codegen Pipeline Analysis

The `PipelineAnalysis` struct (exported from `generate_parser_with_analysis()`)
bridges the PraTTaIL parser pipeline to the macros crate's Ascent codegen:

```text
  PipelineAnalysis {
      dead_rule_labels:     HashSet<String>           → Ascent DCE (Sprint 1)
      constructor_weights:  HashMap<String, f64>      → Rule ordering (Sprint 3)
      category_weights:     HashMap<String, f64>      → Category ordering
      isomorphic_groups:    Vec<Vec<String>>           → Template instantiation (Sprint 8)
      decision_trees:       HashMap<String, CDT>      → Composition analysis
  }
```

The macros crate's `generate_ascent_source()` consumes this analysis to:
- Skip Ascent rules for dead constructors (ART06 + A4)
- Order match arms by constructor weight (cache locality)
- Order rules by category weight (frequent categories first)
- Detect isomorphic WFST groups for `macro_rules!` templates

---

*Source files:*
[`prattail/src/cost_benefit.rs`](../../src/cost_benefit.rs),
[`macros/src/logic/mod.rs`](../../../macros/src/logic/mod.rs),
[`macros/src/logic/equations.rs`](../../../macros/src/logic/equations.rs),
[`macros/src/logic/fusion.rs`](../../../macros/src/logic/fusion.rs),
[`macros/src/logic/bloom_filter.rs`](../../../macros/src/logic/bloom_filter.rs),
[`docs/design/codegen-optimization-catalog.md`](../../../docs/design/codegen-optimization-catalog.md)
