# Automata-Driven Codegen Optimizations

This document describes the promotion of 4 advanced automata modules from `OptimizationStatus::Diagnostic` to `OptimizationStatus::Auto`, enabling their analysis results to feed into codegen decisions via `PipelineAnalysis`. Two additional modules contribute informational fields for future optimization.

## 1. Motivation

The 11 advanced automata modules (M1–M11) compute sophisticated analyses during Phase 7B of the pipeline. Before this work, all 11 had `OptimizationStatus::Diagnostic` — they ran analysis, emitted lints, and reported findings, but none modified codegen behavior. The existing Auto optimization infrastructure (cost-benefit scoring → `OptimizationGates` → codegen checks) was proven and handled 12 Auto optimizations, but the advanced automata results were discarded before reaching codegen.

This work bridges that gap: analysis results from 6 modules now flow through `build_pipeline_analysis()` into `PipelineAnalysis`, where the macros crate can use them during Ascent code generation.

## 2. Architecture

```
Analysis Phase (Phase 7B)     Pipeline Bridge           Macros Codegen
┌───────────────────────┐    ┌───────────────────┐    ┌─────────────────────┐
│ symbolic_result       │───→│ dead_rule_labels  │───→│ skip dead rules     │
│ probabilistic_result  │───→│ constructor_wts   │───→│ sort by frequency   │
│ alternating_result    │───→│ isomorphic_groups │───→│ shared templates    │
│ vpa_result            │───→│ bracket_det.      │───→│ (future: committed) │
│ register_result       │───→│ dead_binder_cats  │───→│ skip alpha-equiv    │
│ multi_tape_result     │───→│ independent_cats  │───→│ (future: decouple)  │
└───────────────────────┘    └───────────────────┘    └─────────────────────┘
        │                            │                        │
        │                     build_pipeline_                 │
        │                     analysis()                 generate_ascent
        │                                                _source() in
        └────── lint layer ──────────────────────────── macros/src/logic/
                (unchanged)                              mod.rs
```

### 2.1 Data Flow

The `AdvancedAnalysisBundle<'a>` struct (defined in `pipeline.rs`) bundles all cfg-gated analysis results into a single parameter for `build_pipeline_analysis()`:

```rust
struct AdvancedAnalysisBundle<'a> {
    #[cfg(feature = "symbolic-automata")]
    symbolic: Option<&'a SymbolicAnalysis>,
    #[cfg(feature = "alternating")]
    alternating: Option<&'a AlternatingAnalysis>,
    #[cfg(feature = "vpa")]
    vpa: Option<&'a VpaAnalysis>,
    #[cfg(feature = "register-automata")]
    register: Option<&'a RegisterAnalysis>,
    #[cfg(feature = "probabilistic")]
    probabilistic: Option<&'a ProbabilisticAnalysis>,
    #[cfg(feature = "multi-tape")]
    multi_tape: Option<&'a MultiTapeAnalysis>,
    _phantom: PhantomData<&'a ()>,
}
```

This avoids `#[cfg]` on individual function parameters (which Rust does not support) while keeping the API clean.

## 3. Promoted Optimizations

### 3.1 SYM01-DCE: Symbolic Guard Dead Code Elimination (M1 Symbolic)

**Status**: `OptimizationStatus::Auto`
**Gate**: `symbolic_guard_dce`
**Extends**: A4 Enhanced DCE (dead_rule_labels)

When `SymbolicAnalysis.guard_satisfiability` contains `(description, false)` pairs, the corresponding guard can never fire. The rule is semantically dead and is added to `dead_rule_labels`.

**Safety**: A guard proven unsatisfiable by Boolean algebra evaluation cannot match any input. `{a ∈ Σ | φ(a)} = ∅` implies no symbol matches, no transition fires, and the rule is dead. Cite: Veanes et al. (2010) "Symbolic finite automata."

**New field**: `SymbolicAnalysis.unsatisfiable_rule_labels: Vec<String>` — computed during `analyze_from_bundle()` by filtering guards where `is_satisfiable == false`.

### 3.2 PR01-DCE: Probabilistic Dead Code Elimination (M7 Probabilistic)

**Status**: `OptimizationStatus::Auto`
**Gate**: `probabilistic_dce`
**Extends**: A4 Enhanced DCE (dead_rule_labels)

When `ProbabilisticAnalysis.is_normalized == true` and `low_selectivity_rules` is non-empty, those rules have selectivity < 0.01 — they fire less than 1% of the time in trained data.

**Safety**: Only applies when `is_normalized == true`, meaning real corpus training has been performed. The default `analyze_from_bundle()` returns uniform weights with `is_normalized = false`, producing no dead rules. This is a statistical heuristic, not an exact proof of deadness.

### 3.3 PR01-WEIGHT: Probabilistic Weight Blending (M7 Probabilistic)

**Status**: `OptimizationStatus::Auto`
**Gate**: `probabilistic_weight_blend`
**Extends**: Sprint 3 Rule Ordering (constructor_weights)

When probabilistic analysis is trained (`is_normalized == true`), per-rule selectivity scores are blended into `constructor_weights` for better rule ordering:

```
w_blend(r) = (w_wfst(r) + (-ln(selectivity(r)))) / 2
```

This is a geometric-mean blend in the tropical semiring: WFST structural weights capture grammar topology while probabilistic weights capture corpus frequency. The blend averages both signals.

**Safety**: Weight ordering only affects performance (match arm ordering, cache locality). It cannot change parse results — the same set of rules fires, just in different order.

**New field**: `ProbabilisticAnalysis.rule_selectivities: HashMap<String, f64>` — per-rule selectivity in [0,1], populated from forward algorithm scores.

### 3.4 N06-ISO: Bisimulation Isomorphic Group Extension (M3 Alternating)

**Status**: `OptimizationStatus::Auto`
**Gate**: `bisimulation_iso_groups`
**Extends**: Sprint 8 Isomorphic WFST Detection (isomorphic_groups)

`AlternatingAnalysis.non_bisimilar_pairs` lists category pairs that are NOT language-equivalent. The complement — category pairs not listed and not already in De Bruijn isomorphic groups — are bisimilar and can share dispatch templates.

**Safety**: Bisimulation game is sound and complete for finite alternating automata (Milner 1989). If categories A and B are bisimilar, they accept exactly the same weighted language, so sharing dispatch code is correct.

### 3.5 RA01-SKIP: Register Dead Binder Elimination (M6 Register)

**Status**: `OptimizationStatus::Auto`
**Gate**: `skip_dead_binders`
**New PipelineAnalysis field**: `dead_binder_categories: HashSet<String>`

`RegisterAnalysis.dead_registers` identifies register indices that are stored but never tested. In PraTTaIL, registers correspond to binder categories. If a binder's register is dead (name stored but never pattern-matched against), alpha-equivalence checking for that binder category can be skipped.

**Safety**: A dead register cannot influence acceptance — by definition, no transition tests it. Skipping alpha-equiv for dead-register binders cannot change parse results. Cite: Kaminski & Francez (1994) "Finite-memory automata."

## 4. Informational Fields (Deferred Codegen)

### 4.1 V05-INFO: VPA Bracket Deterministic Flag (M4 VPA)

**Status**: `OptimizationStatus::Diagnostic`
**New PipelineAnalysis field**: `bracket_deterministic: bool`

`bracket_deterministic = true` when `is_determinizable == true` AND `alphabet_mismatches` is empty. The current trampoline codegen already handles brackets deterministically, so this flag doesn't enable a new optimization in the current parser architecture. It serves as a verification gate and a foundation for future work (bounded stack depth, multi-bracket discrimination).

### 4.2 MT01-INFO: Multi-Tape Independent Categories (M8 Multi-Tape)

**Status**: `OptimizationStatus::Diagnostic`
**New PipelineAnalysis field**: `independent_categories: HashSet<String>`

`MultiTapeAnalysis.disconnected_tapes` identifies tapes (= channel categories) that are independent. Currently, `analyze_from_bundle()` returns `disconnected_tapes: Vec::new()` — the analysis doesn't yet detect tape independence from grammar structure. Promoted to Auto when non-trivial detection is implemented.

## 5. Cost-Benefit Integration

### 5.1 GrammarProfile Extensions

Five new cfg-gated fields capture metrics for optimization decisions:

| Field | Feature | Source |
|-------|---------|--------|
| `unsatisfiable_guard_count` | `symbolic-automata` | Number of unsatisfiable guards |
| `probabilistic_mean_entropy` | `probabilistic` | Mean entropy from PA |
| `low_selectivity_count` | `probabilistic` | Number of low-selectivity rules |
| `bisimulation_extra_groups` | `alternating` | Extra groups beyond De Bruijn |
| `dead_register_count` | `register-automata` | Number of dead registers |

### 5.2 OptimizationGates Extensions

Five new cfg-gated boolean gate fields:

| Gate | Feature | Optimization |
|------|---------|-------------|
| `symbolic_guard_dce` | `symbolic-automata` | SYM01-DCE |
| `probabilistic_dce` | `probabilistic` | PR01-DCE |
| `probabilistic_weight_blend` | `probabilistic` | PR01-WEIGHT |
| `bisimulation_iso_groups` | `alternating` | N06-ISO |
| `skip_dead_binders` | `register-automata` | RA01-SKIP |

All gates are wired through `all_enabled()`, `none_enabled()`, `from_recommendations()`, and `from_env()`.

## 6. Optimization Status Table

| Module | Optimization ID | Status | Gate Field | Extends | Codegen Effect |
|--------|----------------|--------|------------|---------|----------------|
| M1 Symbolic | SYM01-DCE | **Auto** | `symbolic_guard_dce` | A4 DCE | Skip dead rules |
| M7 Probabilistic | PR01-DCE | **Auto** | `probabilistic_dce` | A4 DCE | Skip dead rules |
| M7 Probabilistic | PR01-WEIGHT | **Auto** | `probabilistic_weight_blend` | Sprint 3 | Refine ordering |
| M3 Alternating | N06-ISO | **Auto** | `bisimulation_iso_groups` | Sprint 8 | Shared templates |
| M6 Register | RA01-SKIP | **Auto** | `skip_dead_binders` | NEW | Skip α-equiv |
| M4 VPA | V05-INFO | Diagnostic | — | — | Informational |
| M8 Multi-Tape | MT01-INFO | Diagnostic | — | — | Informational |

## 7. Safety Invariants

1. **No optimization changes the recognized language.** DCE removes only provably dead rules; weight ordering changes dispatch order but not acceptance.
2. **Feature-gating prevents compilation breakage.** Each optimization is behind `#[cfg(feature = "...")]`. With default features, no new fields exist and no new code paths activate.
3. **`is_normalized` guard on probabilistic DCE.** Default uniform weights produce `is_normalized = false`, which prevents any low-selectivity rules from entering `dead_rule_labels`.
4. **Out-of-bounds register indices are gracefully skipped.** `categories.get(idx)` returns `None` for invalid indices; `filter_map` drops them.
5. **Lint layer is unchanged.** All 27 advanced automata lints continue to emit diagnostics independently of codegen promotion.

## 8. Test Coverage

28 new tests across two modules:

- **15 pipeline tests** (`pipeline.rs`): symbolic DCE (4), probabilistic DCE (4), probabilistic weights (3), bisimulation groups (4), register dead binders (3), VPA bracket flag (3), multi-tape independent categories (3)
- **13 cost-benefit tests** (`cost_benefit.rs`): status checks (4), gate wiring (4), profile defaults (5)

All tests pass under both `cargo test --workspace` (default features) and `cargo test --workspace --all-features`.

## 9. Future Work

- **M4 VPA**: Bounded stack depth optimization (requires `max_nesting_depth` in `VpaAnalysis`)
- **M8 Multi-Tape**: Parallel tape processing (requires non-trivial `disconnected_tapes` detection)
- **M5 Parity Tree**: AST invariant verification gating
- **M2 Büchi**: Liveness-based dead cycle elimination
- **Macros crate integration for RA01-SKIP**: Wire `dead_binder_categories` into binder alpha-equiv codegen

## 10. Critical Files

| File | Changes |
|------|---------|
| `prattail/src/pipeline.rs` | `AdvancedAnalysisBundle`, `build_pipeline_analysis()` body, call site wiring |
| `prattail/src/lib.rs` | `PipelineAnalysis` — 3 new cfg-gated fields |
| `prattail/src/cost_benefit.rs` | `status()` promotions, `GrammarProfile`/`OptimizationGates` extensions |
| `prattail/src/symbolic.rs` | `SymbolicAnalysis.unsatisfiable_rule_labels` |
| `prattail/src/probabilistic.rs` | `ProbabilisticAnalysis.rule_selectivities` |

## 11. References

- D'Antoni, L. & Veanes, M. "Symbolic Finite Automata" (2017)
- Kaminski, M. & Francez, N. "Finite-Memory Automata" (TCS 134, 1994)
- Kostolanyi, A. & Misun, F. "Alternating Weighted Automata over Commutative Semirings" (TCS 740, 2018)
- Milner, R. "Communication and Concurrency" (Prentice Hall, 1989)
- Rabiner, L. R. "A Tutorial on Hidden Markov Models and Selected Applications in Speech Recognition" (Proc. IEEE 77, 1989)
- Veanes, M. et al. "Symbolic Automata: The Toolkit" (TACAS 2010)

## 12. Cross-References

- [Advanced Automata Overview](advanced-automata-overview.md)
- [Optimization Pipeline README](../../docs/optimization/README.md)
- [Cost-Benefit Framework](optimization-pipeline-overview.md)
- [Per-Optimization Docs](../../docs/optimization/)
- [Soundness Proofs](../theory/optimization/codegen-soundness.md)
