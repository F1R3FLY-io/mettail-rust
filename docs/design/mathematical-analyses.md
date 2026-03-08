# Mathematical Analyses & Theorem Proving in MeTTaIL

## Overview

MeTTaIL's `language!` macro substrate supports formal reasoning through:
- Equational logic (bidirectional `eq_cat` with congruence closure)
- Term rewriting (directional `rw_cat` with congruence propagation)
- Fixpoint computation (Ascent semi-naive evaluation)
- WPDS poststar/prestar reachability over 15 semirings
- Forward-backward algorithm (inside/outside over any semiring)
- `matrix_star()` transitive closure (generalized Floyd-Warshall)

This document covers the mathematical analysis infrastructure added to extend
these capabilities into theorem proving, model checking, and formal verification.

## Architecture

```
                          ┌──────────────────────────────────────────┐
                          │       MeTTaIL language! Specification    │
                          │  terms { } equations { } rewrites { }   │
                          │  logic { }                               │
                          └─────────────┬────────────────────────────┘
                                        │
                ┌───────────────────────┼───────────────────────┐
                │                       │                       │
                ▼                       ▼                       ▼
    ┌───────────────────┐  ┌────────────────────┐  ┌───────────────────────┐
    │   String-Level    │  │    Tree-Level      │  │   Semantic-Level      │
    │   Automata        │  │    Automata        │  │   Analysis            │
    ├───────────────────┤  ├────────────────────┤  ├───────────────────────┤
    │ NFA/DFA (lexer)   │  │ WTA (term recog.)  │  │ Ascent fixpoint       │
    │ WFST (dispatch)   │  │                    │  │ eq/rw/path relations  │
    │ VPA (structured)  │  │                    │  │ Provenance semiring   │
    │ Buchi (liveness)  │  │                    │  │ KAT (Hoare logic)     │
    └────────┬──────────┘  └────────┬───────────┘  └───────────┬───────────┘
             │                      │                          │
             ▼                      ▼                          ▼
    ┌────────────────────────────────────────────────────────────────────┐
    │                   Pushdown-Level Analysis                         │
    │  WPDS: poststar / prestar / stringsum                            │
    │  EWPDS: merging functions for local variable analysis            │
    │  VPA: decidable equivalence/inclusion                            │
    │  WPDS x Buchi: LTL model checking                                │
    └────────────────────────────────┬───────────────────────────────────┘
                                     │
                                     ▼
    ┌────────────────────────────────────────────────────────────────────┐
    │                 Concurrency-Level Analysis                        │
    │  Petri nets: deadlock, mutual exclusion, boundedness             │
    │  Alternating automata: bisimulation games, CTL                   │
    │  Nominal automata: fresh name analysis                           │
    └────────────────────────────────┬───────────────────────────────────┘
                                     │
                                     ▼
    ┌────────────────────────────────────────────────────────────────────┐
    │              Semiring Layer (shared by ALL levels)                │
    │  15+ semirings: Boolean, Tropical, Counting, Log, Entropy,       │
    │  Viterbi, Arctic, Fuzzy, Truncation, Amplitude, Edit,            │
    │  Product, Context, Complexity, Nbest, Provenance, Relational     │
    │  + StarSemiring trait + matrix_star() + forward-backward          │
    └──────────────────────────────────────────────────────────────────┘
```

## Feature Gates

All new analysis modules are feature-gated to preserve the ~55s default build:

| Feature | Module(s) | Purpose |
|---------|-----------|---------|
| `provenance` | `provenance.rs` | Polynomial semiring N[X] — proof tracking |
| `proofs` | `proof_output.rs` | Layered proof output (human-readable + Rocq) |
| `wpds-relational` | `relational.rs` | Binary relation semiring for SLAM/BLAST |
| `wpds-extended` | `ewpds.rs` | EWPDS merging functions |
| `wpds-ara` | `ara.rs` | Affine-Relation Analysis weight domain |
| `trs-analysis` | `confluence.rs`, `termination.rs` | Critical pairs, dependency pairs |
| `vpa` | `vpa.rs` | Visibly Pushdown Automata |
| `tree-automata` | `tree_automaton.rs` | Weighted Tree Automata |
| `omega` | `buchi.rs` | Buchi automata |
| `ltl` | `ltl.rs` | LTL model checking |
| `alternating` | `alternating.rs` | Alternating automata |
| `nominal` | `nominal.rs` | Nominal automata |
| `petri` | `petri.rs` | Petri nets / VASS |
| `cra` | `cra.rs` | Cost Register Automata |
| `kat` | `kat.rs` | Kleene Algebra with Tests |
| `morphisms` | `morphism.rs` | Theory morphisms |

### Convenience Groups

| Gate | Activates |
|------|-----------|
| `analysis` | `tree-automata` + `vpa` + `trs-analysis` |
| `verification` | `omega` + `ltl` + `kat` + `wpds-relational` |
| `process-algebra` | `nominal` + `petri` + `omega` + `alternating` |
| `full-analysis` | all gates |

### Always-On Modules

| Module | Purpose |
|--------|---------|
| `verify.rs` | Safety verification API (WPDS prestar vs. bad states) |
| `repair.rs` | Repair suggestion engine (semiring-ranked fixes) |
| `cegar.rs` | CEGAR loop: iterative abstraction refinement |
| `newton.rs` | Newton's method for semiring fixpoints |
| `tensor.rs` | Tensor product semirings (correlated analyses) |
| `algebraic.rs` | Algebraic program analysis (Tarjan path expressions) |

## Module Summary

### Phase 1: Foundations

- **`provenance.rs`** — Polynomial semiring N[X] (Green et al. 2007). Tracks HOW
  facts are derived. `ProvenanceWeight` supports `plus` (union of derivations),
  `times` (conjunction of derivation steps), and `evaluate()` to collapse
  provenance to any concrete semiring via a valuation homomorphism.

- **`relational.rs`** — Binary relation semiring on finite sets (Reps et al. 2007,
  Def. 7). `RelationalWeight<G>` with `HeapSemiring` trait (non-Copy). Enables
  SLAM/BLAST-style Boolean program analysis via WPDS.

- **`ewpds.rs`** — Extended WPDS with per-push-rule merge functions. `MergeFunction`
  trait allows combining caller local state with callee global effect at call/return
  boundaries. Handles PNew scoping and PInput binding in Rho calculus.

- **`proof_output.rs`** — Layered proof output. `ProofOutput` carries verdict +
  provenance + proof steps + optional Rocq certificate. Integrates provenance
  tracking with human-readable explanation generation.

- **`verify.rs`** — Safety property verification. `check_safety()` runs prestar
  on bad-state automata. `build_bad_state_automaton()` constructs target P-automata.
  `Verdict` enum (Verified/Violated/Unknown) + `VerificationResult` for structured output.

- **`repair.rs`** — Repair suggestion engine. `RepairSuggestion` with kind, confidence,
  edit cost, alternative count. `RepairSet` supports sorting by different semiring
  criteria (cheapest, most confident, most alternatives).

### Phase 2: Grammar-Level Analysis

- **`confluence.rs`** — Knuth-Bendix critical pair detection. `detect_critical_pairs()`
  finds overlapping LHS patterns, `check_joinability()` tests convergence,
  `check_confluence()` aggregates results.

- **`termination.rs`** — Dependency pair analysis. `extract_dependency_pairs()` finds
  potential recursive calls, `build_dependency_graph()` with Tarjan SCC,
  `check_termination()` uses structural ordering.

- **`vpa.rs`** — Visibly Pushdown Automata. `construct_vpa()` builds from
  call/return pairs. `complement()`, `intersect()`, `check_equivalence()` —
  all decidable for VPAs (closed under all Boolean operations).

### Phase 3: Program-Level Verification

- **`kat.rs`** — Kleene Algebra with Tests. `KatExpr` + `BooleanTest` types.
  `check_equivalence()` via symbolic bisimulation. `verify_hoare_triple()`:
  `{p} e {q}` ↔ `p·e·¬q = 0`.

- **`buchi.rs`** — Buchi automata. `buchi_intersect()` (3-counter product),
  `check_emptiness()` (SCC-based — non-empty iff accepting SCC reachable from initial).

- **`ltl.rs`** — LTL formulas with recursive descent parser. `ltl_to_buchi()`
  for direct constructions (G, F, U, atoms). `check_ltl_property()` via
  negation + Buchi intersection + emptiness.

### Phase 4: Tree & Concurrency Automata

- **`tree_automaton.rs`** — Weighted Tree Automata generic over `Semiring`.
  `bottom_up_evaluate()` leaf-to-root, `top_down_propagate()` root-to-leaf.

- **`alternating.rs`** — Alternating automata with existential/universal branching.
  `check_emptiness()` via bottom-up fixpoint. `bisimulation_game()` via
  attractor computation.

- **`petri.rs`** — Petri nets. `fire_transition()` + `enabled_transitions()`.
  `check_coverability()` via Karp-Miller tree with omega markers.
  `check_deadlock()` via reachability.

- **`nominal.rs`** — Nominal automata with orbit-finite state spaces.
  `construct_nominal()` with equivariant transition validation.

- **`cra.rs`** — Cost Register Automata. `evaluate_stream()` steps through
  register updates. `cra_check_equivalence()` via bounded testing.

### Phase 5: Meta-Level & Algorithms

- **`morphism.rs`** — Theory morphisms. `construct_morphism()` validates
  sort/op mappings. `verify_preservation()` checks axiom images.
  `translate_term()` recursive term translation.

- **`ara.rs`** — Affine-Relation Analysis (Reps et al. 2007, Section 3.2). Discovers
  all interprocedural affine relationships (`x_i = c_0 + c_1*x_1 + ... + c_n*x_n`).
  `AraWeight` wraps a vector space of (n+1)x(n+1) matrices; `combine()` = span union,
  `extend()` = pairwise matrix product. Basis reduction via Gaussian elimination.
  Subsumes constant propagation, copy-constant, and linear-constant propagation.

- **`newton.rs`** — Newton's method for semiring fixpoints (Esparza, Kiefer &
  Luttenberger 2010). `EquationSystem<W>` represents polynomial systems `X = F(X)`;
  `newton_fixpoint()` converges faster than `kleene_fixpoint()` via Jacobian
  matrix star closure. Generic over any `StarSemiring`.

- **`tensor.rs`** — Tensor product semirings. `TensorWeight<W1, W2>` combines two
  analyses with interaction (unlike independent `ProductWeight`). Sparse
  representation as sum of elementary tensors `w1 ⊗ w2`. Projection and
  conditional marginals. `StarSemiring` impl via bounded power series.

- **`cegar.rs`** — CEGAR loop (Clarke et al. 2000). Walks the abstraction ladder
  `Boolean → Counting → Tropical`, running `prestar` at each level. Spurious
  counterexample detection via concrete trace validation. `CegarLog` records
  full refinement history for diagnostics.

- **`algebraic.rs`** — Algebraic program analysis (Kincaid et al. 2019). Tarjan
  SCC decomposition of control flow graphs into path expressions (regular
  expressions over semiring weights). `evaluate()` computes semiring value;
  `all_pairs_analysis()` via `matrix_star`. Interprocedural extension with
  call/return weight composition.

### Phase 5B: Analysis-Driven Optimizations

- **VPA determinization** (`vpa.rs`): `determinize()`, `is_deterministic()`,
  `reachable_states()`, `trim()` — zero-backtracking parser generation for
  structured sublanguages.

- **WTA hot-path specialization** (`tree_automaton.rs`): `hot_path_analysis()`,
  `specialize()`, `HotPathReport`, `SpecializationCandidate` — frequency-based
  transition ranking and specialized automaton generation for common patterns.

- **Forward-backward hot-path** (`forward_backward.rs`): `hot_path_analysis()`,
  `critical_path()`, `edge_occupancy()` — identify critical edges via
  α(from) ⊗ w(e) ⊗ β(to) expected weight computation.

- **Petri net parallelism** (`petri.rs`): `check_independence()`,
  `independence_relation()`, `extract_parallel_regions()`,
  `analyze_parallelism()` — Bron-Kerbosch maximal clique detection for
  concurrent transition identification.

- **Nominal scope narrowing** (`nominal.rs`): `compute_name_usage()`,
  `analyze_scope()`, `narrow_scope()` — minimal scope computation for
  PNew bindings based on orbit-finite usage analysis.

- **CEGAR adaptive optimization** (`cegar.rs`): `adaptive_dead_rule_elimination()`,
  `adaptive_dispatch_analysis()` — CEGAR-guided dead code identification and
  dispatch determinism classification.

- **Context-sensitive codegen analysis** (`repair.rs`): `analyze_context_dispatch()`
  — identifies categories where different callers enable different rule subsets.

- **Congruence rule fusion analysis** (`repair.rs`): `analyze_congruence_fusion()`
  — groups same-constructor congruence rules for single-match-arm generation.

### Phase 5C: Repair & Completion Engine

- **Grammar completion** (`repair.rs`): `suggest_missing_rules()`,
  `suggest_cross_category_ref()` — FIRST/FOLLOW gap suggestions and dead-rule
  reachability repair.

- **Congruence rule synthesis** (`repair.rs`): `suggest_congruence_rules()` —
  generates per-position congruence rules for constructors that lack them.

- **Confluence repair** (`confluence.rs`): `suggest_confluence_repairs()`,
  `suggest_termination_repair()` — critical pair → equation/rewrite suggestions
  with structural similarity-based confidence.

- **Semiring-ranked repair** (`repair.rs`): `RepairSet.merge()`,
  `filter_by_confidence()`, `filter_by_max_cost()`, `top_n_by_confidence()`,
  `top_n_by_cost()`, `rank_multi_criteria()` — multi-criteria suggestion ranking.

- **Safety repair** (`verify.rs`): `suggest_safety_repairs()`,
  `suggest_invariant_strengthening()` — counterexample-driven guard insertion
  and precondition/postcondition adjustment suggestions.

- **Morphism completion** (`morphism.rs`): `detect_gaps()`,
  `suggest_morphism_completion()` — gap detection + candidate translation
  generation for incomplete theory morphisms.

- **Lint integration** (`repair.rs`): `RepairDiagnostic`, `DiagnosticSeverity`,
  `dead_rule()`, `missing_rule()`, `missing_congruence()` — structured
  diagnostics embedding repair suggestions into the existing lint framework.

### Phase 6: Rocq Verification

Machine-checkable correctness proofs in `formal/rocq/mathematical_analyses/`:

- **`SemiringLaws.v`** (6.1): Semiring type class + proofs for Provenance (N[X]),
  Relational (binary relations), and KAT weight domains.
- **`WpdsCorrectness.v`** (6.2): WPDS model, P-automaton acceptance, poststar/prestar
  correctness (MOVP fixpoint characterization), saturation convergence.
- **`VpaClosureProperties.v`** (6.3): VPA complement, intersection, decidable
  equivalence as a corollary.
- **`KatSoundness.v`** (6.4): KAT denotational semantics, Hoare triple encoding
  soundness: `{p} e {q} ↔ test(p) · e · test(¬q) = 0`.
- **`BuchiWpdsProduct.v`** (6.5): Buchi × WPDS product construction, SCC-based
  emptiness soundness.

## Test Counts

| Feature Set | Tests |
|-------------|-------|
| Default features | 1,764 |
| All features (`--all-features`) | 2,346 |
| New modules (Phase 1-5, 5B, 5C) | ~620 |

## Detailed Documentation

### Design Documents

- [Framework Overview](../../prattail/docs/design/analysis/README.md) — Module taxonomy, feature gates, semiring matrix
- [TRS Analysis](../../prattail/docs/design/analysis/trs-analysis.md) — Confluence and termination
- [Pushdown Verification](../../prattail/docs/design/analysis/pushdown-verification.md) — Safety, CEGAR, EWPDS, ARA
- [Automata Extensions](../../prattail/docs/design/analysis/automata-extensions.md) — VPA, WTA, Buchi, alternating
- [Concurrency Analysis](../../prattail/docs/design/analysis/concurrency-analysis.md) — Petri, nominal, bisimulation
- [Temporal & Provenance](../../prattail/docs/design/analysis/temporal-and-provenance.md) — LTL, N[X], CRA
- [Meta-Level](../../prattail/docs/design/analysis/meta-level-analysis.md) — Morphisms, KAT, tensor, repair

### Formal Verification

- [Rocq Proofs Overview](../../prattail/docs/theory/formal-verification/README.md)
- [Semiring Laws](../../prattail/docs/theory/formal-verification/semiring-laws.md) — SemiringLaws.v
- [WPDS Correctness](../../prattail/docs/theory/formal-verification/wpds-correctness.md) — WpdsCorrectness.v
- [VPA Closure](../../prattail/docs/theory/formal-verification/vpa-closure.md) — VpaClosureProperties.v
- [KAT Soundness](../../prattail/docs/theory/formal-verification/kat-soundness.md) — KatSoundness.v
- [Buchi × WPDS](../../prattail/docs/theory/formal-verification/buchi-wpds-product.md) — BuchiWpdsProduct.v

### Diagnostics

28 analysis-level lint codes: [T01–T04](../../prattail/docs/diagnostics/analysis/trs/), [V01–V04](../../prattail/docs/diagnostics/analysis/automata/), [S01–S06](../../prattail/docs/diagnostics/analysis/safety/), [N01–N05](../../prattail/docs/diagnostics/analysis/concurrency/), [L01–L02](../../prattail/docs/diagnostics/analysis/temporal/), [E01–E02](../../prattail/docs/diagnostics/analysis/extension/), [M01–M02](../../prattail/docs/diagnostics/analysis/morphism/), [K01–K02](../../prattail/docs/diagnostics/analysis/kat/), [P06](../../prattail/docs/diagnostics/analysis/P06-analysis-pipeline-cost.md)

## References

| Ref | Paper |
|-----|-------|
| Reps, Lal & Kidd (2007) | *Program Analysis Using Weighted Pushdown Systems* |
| Green, Karvounarakis & Tannen (2007) | *Provenance Semirings* |
| Alur & Madhusudan (2004) | *Visibly Pushdown Languages* |
| Kozen (1997) | *Kleene Algebra with Tests* |
| Schwoon (2002) | *Model-Checking Pushdown Systems* |
| Esparza et al. (2001) | *Efficient Algorithms for Model Checking Pushdown Systems* |
| Goodman (1999) | *Semiring Parsing* |
| Comon et al. (2007) | *Tree Automata Techniques and Applications* |
| Bojanczyk et al. (2014) | *Automata Theory in Nominal Sets* |
| Esparza & Nielsen (1994) | *Decidability Issues for Petri Nets* |
| Alur et al. (2013) | *Regular Functions and Cost Register Automata* |
| Clarke et al. (2000) | *Counterexample-Guided Abstraction Refinement* |
| Esparza, Kiefer & Luttenberger (2010) | *Newton's Method for omega-Continuous Semirings* |
| Kincaid, Cyphert, Breck & Reps (2019) | *Algebraic Program Analysis* |
