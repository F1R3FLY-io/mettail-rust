# Advanced Automata Infrastructure Overview

This document provides a comprehensive overview of the 11-module advanced automata
infrastructure in PraTTaIL. Each module extends MeTTaIL's capabilities across the
full stack: parsing, lexing, error recovery, disambiguation, verification,
optimization, code generation, and predicated types.

## 1. Architecture Diagram

```
                    ┌─────────────────────────────────────┐
                    │     Surface: Predicated Types       │
                    │  for (@x : halts /\ primes <- ch)  │
                    └──────────────┬──────────────────────┘
                                   │
┌──────────────────────────────────┼──────────────────────────────────┐
│              Weighted MSO Logic (Module 10)                         │
│  Specification language: grammar properties, lint definitions,     │
│  predicate formulas, optimization preconditions                    │
│  ∨→plus, ∧→times, ∃→Σ, ∀→Π  (Droste & Gastin 2007)              │
└──────────────────────────────────┬──────────────────────────────────┘
                                   │
         ┌─────────────────────────┼─────────────────────────┐
         ▼                         ▼                         ▼
┌─────────────────┐  ┌──────────────────────┐  ┌─────────────────┐
│ Symbolic (M1)   │  │ Poly. AWA (M3)       │  │ Parity Tree(M5) │
│ Lexer+WFST      │  │ Game-theoretic       │  │ AST verification│
│ alphabet optim. │  │ disambiguation       │  │ mu-calculus      │
│ Guard analysis  │  │ Ambiguity quant.     │  │ Test generation  │
└────────┬────────┘  └──────────┬───────────┘  └────────┬────────┘
         │                      │                        │
    ┌────┴────┐           ┌─────┴─────┐            ┌─────┴─────┐
    ▼         ▼           ▼           ▼            ▼           ▼
┌───────┐┌───────┐ ┌──────────┐┌──────────┐ ┌──────────┐┌─────────┐
│Buchi  ││VPA    │ │Register  ││Probabil. │ │Multi-Tape││Multiset │
│(M2)   ││(M4)   │ │(M6)      ││(M7)      │ │(M8)      ││(M9)     │
│Stream ││Stack  │ │Context-  ││Statistic.│ │Multi-    ││PPar     │
│parse  ││cost   │ │sensitive ││disambig. │ │stream    ││analysis │
│Liveness││Depth ││Data-aware││Ranking   │ │Parallel  ││Resource │
└───────┘└───────┘ └──────────┘└──────────┘ └──────────┘└─────────┘
                         │
                    ┌────┴─────────────────┐
                    ▼                      ▼
              ┌──────────┐          ┌──────────┐
              │Two-Way   │          │          │
              │(M11)     │◄────────►│Transducer│
              │Bidir.    │          │(existing)│
              │constraint│          │One-way   │
              │propagate │          │passes    │
              └──────────┘          └──────────┘
```

## 2. Progressive Introduction

The 11 modules form a layered architecture. Layers 1--3 below map to increasing
levels of analytical power; each layer builds on the abstractions below it.

### Layer 1: Weighted Extensions (in-place upgrades)

Three existing modules receive weighted generalizations. The key design pattern
is **zero-cost type aliasing**: parameterize existing types over a semiring `W`,
then alias the current unweighted type to `W = BooleanWeight`. All existing tests
pass without modification.

| Module | File | Key Generalization |
|--------|------|--------------------|
| **M2 Weighted Buchi** | `buchi.rs` | `BuchiAutomaton = WeightedBuchiAutomaton<BooleanWeight>` |
| **M3 Weighted Alternating** | `alternating.rs` | `AlternatingAutomaton = WeightedAlternatingAutomaton<BooleanWeight>` |
| **M4 Weighted VPA** | `vpa.rs` | `Vpa = WeightedVpa<BooleanWeight>` |

### Layer 2: Core New Modules (foundational abstractions)

Two modules provide the foundational abstractions on which higher-level analyses
are built.

| Module | File | Core Abstraction |
|--------|------|------------------|
| **M1 Symbolic Automata** | `symbolic.rs` | `BooleanAlgebra` trait -- predicate-labeled transitions over infinite domains |
| **M10 Weighted MSO** | `weighted_mso.rs` | `WeightedMsoFormula` -- logical specification language compiled to automata |

### Layer 3: Extended Analytical Modules

Six new modules provide domain-specific analyses that compose with the
foundational layers.

| Module | File | Domain |
|--------|------|--------|
| **M5 Parity Tree** | `parity_tree.rs` | AST structural verification via mu-calculus |
| **M6 Register** | `register_automata.rs` | Data-aware parsing and binding verification |
| **M7 Probabilistic** | `probabilistic.rs` | Statistical disambiguation and corpus-driven training |
| **M8 Multi-Tape** | `multi_tape.rs` | Synchronized multi-stream computation |
| **M9 Multiset** | `multiset_automata.rs` | Process multiplicity and resource analysis |
| **M11 Two-Way** | `two_way_transducer.rs` | Bidirectional constraint propagation |

## 3. Module Summaries

### M1: Symbolic Automata (`symbolic.rs`)

**Feature gate**: `symbolic-automata` (depends on `kat`)

Symbolic automata replace explicit alphabet transitions with predicate-labeled
transitions. The core abstraction is the `BooleanAlgebra` trait:

```
BooleanAlgebra
  ├── true_pred()    : Predicate           -- top element (all values)
  ├── false_pred()   : Predicate           -- bottom element (no values)
  ├── and(a, b)      : Predicate           -- conjunction
  ├── or(a, b)       : Predicate           -- disjunction
  ├── not(a)         : Predicate           -- negation
  ├── is_satisfiable(a) : bool             -- SAT check
  ├── witness(a)     : Option<Domain>      -- satisfying element
  └── evaluate(p, e) : bool               -- membership test
```

Three concrete algebras are provided:

| Algebra | Predicate | Domain | SAT | Use Case |
|---------|-----------|--------|-----|----------|
| `KatBooleanAlgebra` | `BooleanTest` | `HashMap<String, bool>` | O(2^n) truth table | Propositional guards |
| `IntervalAlgebra` | `IntervalPred` | `i64` | O(k) interval check | Numeric range predicates |
| `CharClassAlgebra` | `CharClassPred` | `char` | O(k) range check | Structural patterns |

Key algorithms: emptiness (BFS + SAT), determinization (minterm-based subset
construction -- D'Antoni & Veanes 2017), minimization (symbolic Hopcroft),
intersection (product + predicate conjunction), equivalence (symmetric difference
emptiness), decidability classification (T1--T4 tier assignment).

**Lints**: SYM01 (unsatisfiable-guard), SYM02 (overlapping-guards), SYM03
(subsumed-guard), SYM04 (non-minimal-guards).

### M2: Weighted Buchi Automata (extend `buchi.rs`)

**Feature gate**: `omega` (existing)

Generalizes the existing `BuchiAutomaton` to `WeightedBuchiAutomaton<W>` where
`W: Semiring`. Transitions carry weights; acceptance is defined by reaching an
accepting SCC and computing the star closure of its cycle weight.

Key operations:
- `total_accepting_weight()` -- Tarjan SCC + `matrix_star()` for cycle weights (`W: StarSemiring`)
- `weighted_intersect()` -- 3-counter product with `w_a.times(&w_b)`
- `complement()` -- Safra construction, restricted to `BooleanWeight`

**Lints**: O01 (weighted-buchi-non-convergent), O02 (weighted-buchi-heavy-cycle).

### M3: Weighted Alternating Automata (extend `alternating.rs`)

**Feature gate**: `alternating` (existing)

Incorporates the polynomial transition formulation from Kostolanyi & Misun (TCS
740, 2018). Key theoretical result: for non-locally-finite semirings (e.g.,
`TropicalWeight`), alternating weighted automata (AWA) are strictly more powerful
than non-alternating WA (Theorem 7.1). This means alternation genuinely adds
expressiveness for cost/optimization analyses.

Design: polynomial transition functions psi[p,c] in S[x_1,...,x_n] over the
semiring. Each monomial is a coefficient times a product of state evaluations.
Two-mode equivalent: states partitioned into Q_oplus (sum/existential) and
Q_otimes (product/universal).

H-polynomial equations (Theorem 6.4): AWA behaviors correspond to systems of
H-polynomial equations, providing fixpoint computation directly applicable to
recursive predicates.

Key operations: `weighted_emptiness()`, `weighted_parity_value()`,
`weighted_bisimulation()`, `evaluate_polynomial(word)`,
`to_h_polynomial_system()`.

**Lints**: N06 (weighted-parity-non-convergent), N07 (weighted-branching-imbalance).

### M4: Weighted VPA (extend `vpa.rs`)

**Feature gate**: `vpa` (existing)

Generalizes VPA transitions to carry semiring weights. The visible stack
discipline means weighted determinization uses macro-states of type
`HashMap<usize, W>` (weighted powersets). At call symbols, push the entire
weighted macro-state; at return, pop and compose.

Key operations: `weighted_determinize()`, `weighted_run(word)`,
`weighted_inclusion()` (requires `W: IdempotentSemiring`).

**Lints**: V05 (weighted-vpa-non-determinizable), V06
(weighted-vpa-inclusion-failure).

### M5: Parity Alternating Tree Automata (`parity_tree.rs`)

**Feature gate**: `parity-tree-automata` (depends on `alternating`, `tree-automata`)

Combines alternation, parity acceptance, and tree structure to express mu-calculus
formulas over parse trees and ASTs. States have a branching mode (existential or
universal) and a priority (natural number). Acceptance is determined by the
parity of the highest priority seen infinitely often along a branch.

The mu-calculus compiler `mu_calculus_to_pata()` bridges user predicates to PATAs:
- mu X corresponds to odd priority (least fixpoint)
- nu X corresponds to even priority (greatest fixpoint)
- diamond corresponds to existential branching
- box corresponds to universal branching

Example: `letprop halt x = forall x'. not(x ->* x')` compiles to
`nu X. box_{->*}(not X)` -- greatest fixpoint, even priority.

Key operations: `check_emptiness()` (Zielonka's recursive parity game),
`check_inclusion()`, `evaluate_term()`, `mu_calculus_to_pata()`.

**Lints**: PT01 (pata-emptiness-violation), PT02 (pata-subsumption), PT03
(pata-high-priority).

### M6: Register Automata (`register_automata.rs`)

**Feature gate**: `register-automata` (depends on `nominal`)

Data-aware finite-state computation with register storage. Each transition
carries a register operation: `Nop`, `Store`, `TestEq`, `TestNeq`, or
`TestFresh`. Registers hold `DataValue`s that can be compared for equality
across transitions.

Equivalence checking reduces to nominal automata via orbit-finite bisimulation
(connecting to the existing `nominal.rs` module).

Key operations: `evaluate(data_word)`, `check_equivalence()`, `normalize()`.

**Lints**: RA01 (unbound-data-reference), RA02 (redundant-register), RA03
(register-equivalence).

### M7: Probabilistic Automata (`probabilistic.rs`)

**Feature gate**: `probabilistic` (depends on `wfst-log`)

Statistical analysis over grammar structures. Uses `LogWeight` as the native
weight domain with per-state normalization constraints
(sum of outgoing weights = 1 in probability domain).

Reuses existing infrastructure heavily: `forward_backward.rs` for forward
algorithm, `training.rs` for Baum-Welch EM, `EntropyWeight` for Shannon entropy,
`ProductWeight<LogWeight, TropicalWeight>` for expected-cost computation.

Key operations: `normalize()`, `probability_of(word)`, `expected_cost(word)`,
`selectivity()`, `entropy()`, `train_from_corpus()`.

**Lints**: PR01 (low-selectivity-rule), PR02 (non-stochastic-state), PR03
(high-entropy-category), PR04 (expected-depth-anomaly).

### M8: Weighted Multi-Tape Automata (`multi_tape.rs`)

**Feature gate**: `multi-tape` (depends on `wfst-log`)

Synchronized multi-stream computation with `K` input tapes (const generic).
Based on Kempe (2004). Each transition carries an array of `K` optional labels
(one per tape, `None` = epsilon). Multi-channel receives
`for (@x <- ch1, @y <- ch2) { P }` map directly: ch1 to tape 1, ch2 to tape 2.

Key operations (from Kempe 2004): `pair(A1, A2)`, `project(tape_idx)`,
`auto_intersect(i, j)`, `multi_tape_intersect()`, `cross_product()`.

**Lints**: MT01 (multi-channel-overlap), MT02 (multi-tape-disconnected).

### M9: Weighted Automata over Multisets (`multiset_automata.rs`)

**Feature gate**: `multiset-automata`

Multiset-weighted computation for process multiplicity and resource analysis.
Based on Muller, Weiss & Lochau (2024). Two weight types:
- `MultisetWeight`: `(N_0^F, pointwise-max, pointwise-add, 0-bar, 1-bar)` --
  maps features to multiplicities
- `TropicalMultisetWeight`: tropical over multisets -- decidable subclass

Connects to `petri.rs` (multiset rewriting as Petri net firing) and
`runtime/src/hashbag.rs` (PPar uses multisets).

Key operations: `multiplicity_of(feature, word)`,
`satisfies_cardinality(constraint)`, `feature_interaction(f1, f2)`,
`tropical_projection()`.

**Lints**: MS01 (unsatisfiable-cardinality), MS02 (redundant-feature-check).

### M10: Weighted MSO Logic (`weighted_mso.rs`)

**Feature gate**: `weighted-mso` (depends on `symbolic-automata`)

The specification language for grammar properties, lint definitions, predicate
formulas, and optimization preconditions. Based on Droste & Gastin (TCS 380,
2007).

**Theoretical foundation**:
- **Theorem 3.7** (Weighted Buchi-Elgot-Trakhtenbrot): K^rec = K^rmso = K^remso
  -- recognizable formal power series coincide with restricted weighted
  MSO-definable series.
- **Corollary 6.5**: For locally finite commutative semirings, equivalence of
  two MSO sentences is decidable.
- **Theorem 7.11**: For weakly bi-aperiodic semirings, K^aper = K^rfo = K^fo
  (first-order definable = aperiodic = star-free).

The formula AST directly encodes the user's predicate language:
- `phi or psi` has semantics `[[phi]] + [[psi]]` (semiring plus)
- `phi and psi` has semantics `[[phi]] . [[psi]]` (semiring times)
- `exists x. phi` has semantics `Sigma_i [[phi]][x->i]`
- `forall x. phi` has semantics `Pi_i [[phi]][x->i]` (restricted)

Key operations: `to_weighted_automaton()`, `from_weighted_automaton()`,
`classify_formula()`, `check_decidability()`, `evaluate_sentence()`,
`evaluate_formula()`, `check_equivalence()`.

**Lints**: MSO01 (unrestricted-universal-set), MSO02 (non-recognizable-step),
MSO03 (equivalent-formulas).

### M11: Weighted Two-Way Transducers (`two_way_transducer.rs`)

**Feature gate**: `two-way-transducer` (depends on `wfst-log`)

Bidirectional weighted transductions based on Feng & Maletti (CAI 2022, Info. &
Computation 293, 2023). States are partitioned into forward (Q_right: head moves
right) and backward (Q_left: head moves left). Input includes endmarkers
(left-triangle, right-triangle) for boundary detection.

Key distinction from `forward_backward.rs`: forward-backward computes
alpha(u) otimes w otimes beta(v) over a fixed DAG. W2T has dynamic head
movement -- the transducer can revisit already-read input, make state-dependent
decisions based on both left and right context, and produce different output
depending on traversal direction.

RhoCalc-specific types: `ChannelConstraint<W>` (forward + backward transducers
for cross-channel predicates), `JoinPatternAnalysis<W>` (optimal channel
consumption order, deadlock cycles, constraint graph).

Key operations: `transduce(input)`, `sum(M1, M2)`, `compose_one_way(fst)`,
`to_one_way()`, `backward_constraint()`, `analyze_join_pattern()`,
`detect_deadlock()`, `diagnose_failure()`.

**Lints**: TW01 (circular-channel-dependency), TW02 (one-way-sufficient), TW03
(constraint-propagation-divergent).

## 4. Benefits Matrix

Each module serves multiple subsystems. The table below shows all 11 modules
against all 8 subsystems.

| Module | Parsing | Lexing | Recovery | Disambiguation | Verification | Optimization | Codegen | Predicates |
|--------|---------|--------|----------|----------------|--------------|--------------|---------|------------|
| **M1 Symbolic** | Symbolic WFST alphabet | CharClass -> SFA | -- | Predicate-merged states | Guard satisfiability | Alphabet compression | -- | BooleanAlgebra trait |
| **M2 W. Buchi** | Stream/REPL parsing | -- | -- | -- | Liveness (progress) | -- | Weighted omega-regular | Infinite behavior |
| **M3 Poly. AWA** | Adversarial worst-case | -- | -- | Game-theoretic ranking | CTL model checking | H-polynomial fixpoints | -- | forall/exists eval |
| **M4 W. VPA** | Recursive descent cost | -- | Stack-bounded repair | -- | Trampoline verification | Call/return optimization | -- | Scope nesting |
| **M5 Parity Tree** | -- | -- | -- | -- | AST invariant checking | Optimization correctness | Test generation | mu-calculus predicates |
| **M6 Register** | Context-sensitive | Stateful lexer modes | Context-aware repair | Data-dependent dispatch | Binding verification | -- | Register codegen | Data-aware predicates |
| **M7 Probabilistic** | -- | -- | Likelihood-ranked repair | Viterbi disambiguation | -- | Expected-case opt. | Corpus-trained weights | Guard selectivity |
| **M8 Multi-Tape** | Multi-stream sync | Parallel tokenization | Multi-stream repair | Cross-stream correlation | -- | Joint optimization | Multi-output codegen | Multi-channel receives |
| **M9 Multiset** | -- | -- | -- | Ambiguity counting | -- | Resource bounding | -- | Cardinality predicates |
| **M10 W. MSO** | Grammar properties | -- | -- | -- | Buchi-Elgot-Trakht. | Precondition checking | Lint-as-formula | Predicate specification |
| **M11 W. 2-Way** | Join pattern reorder | -- | Bidirectional repair | Cross-channel disambig. | Protocol verification | Constraint propagation | Source-to-source | Cross-channel predicates |

### Reading the matrix

- **Parsing**: How the module extends MeTTaIL's Pratt/RD/trampoline parser.
- **Lexing**: How the module extends the DFA-based lexer pipeline.
- **Recovery**: How the module improves error recovery strategies.
- **Disambiguation**: How the module helps resolve ambiguous grammars.
- **Verification**: What correctness properties the module can check.
- **Optimization**: What performance improvements the module enables.
- **Codegen**: How the module influences generated parser/lexer code.
- **Predicates**: How the module serves the predicated types feature.

## 5. Feature Gate Dependency Graph

```
                       ┌────────────┐
                       │  wfst-log  │
                       └──┬─┬─┬────┘
                          │ │ │
         ┌────────────────┘ │ └────────────────┐
         ▼                  ▼                  ▼
  ┌──────────────┐  ┌──────────────┐  ┌──────────────────┐
  │ probabilistic│  │  multi-tape  │  │two-way-transducer│
  └──────────────┘  └──────────────┘  └──────────────────┘

  ┌──────┐
  │ kat  │
  └──┬───┘
     ▼
  ┌──────────────────┐
  │ symbolic-automata│
  └──────┬───────────┘
         ▼
  ┌──────────────┐
  │ weighted-mso │
  └──────────────┘

  ┌─────────────┐    ┌──────────────┐
  │ alternating │    │tree-automata │
  └──────┬──────┘    └──────┬───────┘
         │                  │
         └────────┬─────────┘
                  ▼
        ┌───────────────────┐
        │parity-tree-automata│
        └───────────────────┘

  ┌──────────┐
  │ nominal  │
  └─────┬────┘
        ▼
  ┌──────────────────┐
  │register-automata │
  └──────────────────┘

  ┌────────────────────┐    (no dependencies)
  │ multiset-automata  │
  └────────────────────┘
```

### Convenience Groups

| Group | Features Included |
|-------|-------------------|
| `analysis` | `tree-automata`, `vpa`, `trs-analysis` |
| `verification` | `omega`, `ltl`, `kat`, `wpds-relational` |
| `process-algebra` | `nominal`, `petri`, `omega`, `alternating`, `symbolic-automata`, `two-way-transducer` |
| `predicated-types` | `symbolic-automata`, `weighted-mso`, `parity-tree-automata`, `register-automata`, `multi-tape`, `multiset-automata`, `two-way-transducer` |
| `full-analysis` | All of the above + `wfst-log`, `quantum`, `wpds-*`, `provenance`, `proofs`, `trs-analysis`, `cra`, `morphisms`, `probabilistic` |

## 6. Integration Flow Through the Pipeline

The advanced automata modules integrate into MeTTaIL's pipeline at well-defined
points. The integration follows the same pattern established by the existing
mathematical analysis modules.

### 6.1 Pipeline Integration (`pipeline.rs`)

All 11 analyses are spawned as parallel threads in `run_math_analyses_parallel()`.
Results are collected into `MathAnalysisResults`, which carries one
`Option<AnalysisType>` field per module:

```
MathAnalysisResults {
    ...existing fields...
    // ── Advanced automata analyses ──
    #[cfg(feature = "symbolic-automata")]
    symbolic_result:     Option<SymbolicAnalysis>,
    #[cfg(feature = "omega")]
    buchi_result:        Option<BuchiAnalysis>,
    #[cfg(feature = "weighted-mso")]
    mso_result:          Option<MsoAnalysis>,
    #[cfg(feature = "probabilistic")]
    probabilistic_result: Option<ProbabilisticAnalysis>,
    #[cfg(feature = "register-automata")]
    register_result:     Option<RegisterAnalysis>,
    #[cfg(feature = "parity-tree-automata")]
    parity_tree_result:  Option<ParityTreeAnalysis>,
    #[cfg(feature = "multi-tape")]
    multi_tape_result:   Option<MultiTapeAnalysis>,
    #[cfg(feature = "multiset-automata")]
    multiset_result:     Option<MultisetAnalysisResult>,
    #[cfg(feature = "two-way-transducer")]
    two_way_result:      Option<TwoWayAnalysis>,
}
```

### 6.2 Lint Integration (`lint.rs`)

Each analysis result feeds into the lint layer via `LintContext` fields. The 34
new lints follow the existing pattern: a lint function reads the analysis result,
checks conditions, and emits `LintDiagnostic` structs via `emit_diagnostic()`.

### 6.3 Cost-Benefit Integration (`cost_benefit.rs`)

Eleven new `Optimization` enum variants gate the analyses:

| Variant | Feature Gate | Primary Lint |
|---------|-------------|-------------|
| `SymbolicGuardAnalysis` | `symbolic-automata` | SYM01--04 |
| `WeightedBuchiAnalysis` | `omega` | O01--02 |
| `WeightedAlternatingAnalysis` | `alternating` | N06--07 |
| `WeightedVpaAnalysis` | `vpa` | V05--06 |
| `ParityTreeAnalysis` | `parity-tree-automata` | PT01--03 |
| `RegisterAnalysis` | `register-automata` | RA01--03 |
| `ProbabilisticAnalysis` | `probabilistic` | PR01--04 |
| `MultiTapeAnalysis` | `multi-tape` | MT01--02 |
| `MultisetAnalysis` | `multiset-automata` | MS01--02 |
| `WeightedMsoAnalysis` | `weighted-mso` | MSO01--03 |
| `TwoWayTransducerAnalysis` | `two-way-transducer` | TW01--03 |

Each variant is evaluated in `evaluate_optimizations()` with feature-gated
`#[cfg(...)]` blocks that assess cost/benefit based on the `GrammarProfile`.

## 7. Module Composition Patterns

The 11 modules are designed to compose with each other and with the existing
infrastructure. Below are the principal composition patterns.

### 7.1 Symbolic + MSO: Guard Specification and Compilation

The `BooleanAlgebra` trait from `symbolic.rs` provides the predicate algebra.
`weighted_mso.rs` uses it to compile MSO formulas into symbolic automata. The
composition flow:

```
User predicate:  for (@x : halts /\ primes <- ch)
       │
       ▼
WeightedMsoFormula  (weighted_mso.rs)
   And(
     AtomicPos("halts", "x"),
     AtomicPos("primes", "x")
   )
       │
       ▼  to_weighted_automaton()
SymbolicAutomaton<KatBooleanAlgebra>  (symbolic.rs)
       │
       ▼  classify_decidability()
Tier assignment: T1/T2/T3/T4
```

### 7.2 Alternating + Parity Tree: Game-Theoretic AST Verification

The `BranchingMode` from `alternating.rs` is reused by `parity_tree.rs` for
tree-level alternation. A PATA state uses the same existential/universal
distinction, extended with parity priorities.

```
alternating.rs: BranchingMode { Existential, Universal }
       │
       ▼  (reuse)
parity_tree.rs: ParityTreeState {
    branching: BranchingMode,
    priority: u32,
}
```

### 7.3 Probabilistic + Forward-Backward: Corpus-Driven Training

The `probabilistic.rs` module delegates heavily to existing infrastructure:

```
probabilistic.rs: train_from_corpus(examples)
       │
       ├──► forward_backward.rs:  forward()/backward() for alpha/beta values
       ├──► training.rs:          Baum-Welch EM iteration
       ├──► semiring.rs:          LogWeight for log-domain arithmetic
       └──► semiring.rs:          EntropyWeight for Shannon entropy
```

### 7.4 Register + Nominal: Data-Aware Binding Analysis

Register automata reduce to nominal automata for equivalence checking:

```
register_automata.rs: check_equivalence(ra1, ra2)
       │
       ▼  reduce to orbit-finite sets
nominal.rs:  nominal bisimulation check
```

### 7.5 Multi-Tape + Compose: Cross-Grammar Constraints

Multi-tape automata extend the existing `compose.rs` module with synchronized
cross-grammar constraints:

```
compose.rs:  compose_languages!(grammar_a, grammar_b)
       │
       ▼  (with multi-tape feature)
multi_tape.rs:  pair(wfst_a, wfst_b) -> WeightedMultiTapeAutomaton<W, 2>
       │
       ▼  auto_intersect(0, 1)
Constrained 2-tape automaton (shared-label synchronization)
```

### 7.6 Two-Way + Transducer: Bidirectional Optimization Passes

Two-way transducers extend the existing `OptimizationPass` trait:

```
transducer.rs:  trait OptimizationPass { fn apply(&self, fst: &Fst) -> Fst }
       │
       ▼  (extend)
two_way_transducer.rs:
    TwoWayOptimizationPass {
        forward_pass:  identify candidates
        backward_pass: validate safety
    }
```

### 7.7 Multiset + Petri: Resource Analysis Bridge

Multiset weights directly model Petri net markings:

```
multiset_automata.rs: MultisetWeight { features: HashMap<String, u64> }
       │
       ▼  (isomorphism)
petri.rs:  Marking (multiset of tokens on places)
```

## 8. Semiring Connections

Each module uses specific semirings from the existing catalog:

| Module | Primary Semiring | Secondary Semirings |
|--------|-----------------|---------------------|
| M1 Symbolic | `BooleanWeight` | -- |
| M2 W. Buchi | Parameterized `W: Semiring` | `TropicalWeight` (StarSemiring required) |
| M3 Poly. AWA | Parameterized `W: Semiring` | `TropicalWeight`, `CountingWeight` |
| M4 W. VPA | Parameterized `W: Semiring` | `TropicalWeight` (IdempotentSemiring for inclusion) |
| M5 Parity Tree | Parameterized `W: Semiring` | -- |
| M6 Register | Parameterized `W: Semiring` | `BooleanWeight` |
| M7 Probabilistic | `LogWeight` | `EntropyWeight`, `ProductWeight<LogWeight, TropicalWeight>` |
| M8 Multi-Tape | Parameterized `W: Semiring` | `LogWeight` (training) |
| M9 Multiset | `MultisetWeight` (new) | `TropicalMultisetWeight` (new) |
| M10 W. MSO | Parameterized (commutative K) | All locally-finite semirings |
| M11 Two-Way | Parameterized `W: Semiring` | `TropicalWeight` (cost analysis) |

Two new semiring types are introduced by M9:
- `MultisetWeight` -- multiset over features with pointwise operations
- `TropicalMultisetWeight` -- tropical (min-plus) over multiset features

See [semiring-catalog.md](semiring-catalog.md) for the full catalog.

## 9. Implementation Sequencing

### Phase 1: Weighted Extensions (in-place, lower risk)

| Sprint | Module | File | New LOC | Refactored |
|--------|--------|------|---------|------------|
| 1 | Weighted VPA | `vpa.rs` | ~500 | ~150 |
| 2 | Weighted Buchi | `buchi.rs` | ~400 | ~100 |
| 3 | Weighted Alternating | `alternating.rs` | ~500 | ~80 |

### Phase 2: Core New Modules (foundational)

| Sprint | Module | File | New LOC |
|--------|--------|------|---------|
| 4 | Symbolic Automata | `symbolic.rs` | ~1,800 |
| 5 | Weighted MSO Logic | `weighted_mso.rs` | ~700 |

### Phase 3: Extended New Modules

| Sprint | Module | File | New LOC |
|--------|--------|------|---------|
| 6 | Probabilistic Automata | `probabilistic.rs` | ~900 |
| 7 | Register Automata | `register_automata.rs` | ~700 |
| 8 | Parity Tree Automata | `parity_tree.rs` | ~800 |

### Phase 4: Multi-domain Modules

| Sprint | Module | File | New LOC |
|--------|--------|------|---------|
| 9 | Multi-Tape Automata | `multi_tape.rs` | ~600 |
| 10 | Multiset Automata | `multiset_automata.rs` | ~500 |
| 10B | Weighted Two-Way | `two_way_transducer.rs` | ~800 |

### Phase 5: Integration and Decidability

| Sprint | Task | Files |
|--------|------|-------|
| 11 | Pipeline wiring + 34 lints + cost-benefit | `pipeline.rs`, `lint.rs`, `cost_benefit.rs`, `lib.rs`, `Cargo.toml` |
| 12 | Decidability classifier (T1--T4) + predicate AST | `weighted_mso.rs`, `symbolic.rs` |
| 13 | Documentation | `prattail/docs/` |
| 14 | Rocq proofs | `formal/rocq/` |

### Totals

| Metric | Value |
|--------|-------|
| New modules | 8 |
| Modified modules | 3 |
| Integration files | 5 |
| New LOC | ~8,000 |
| Refactored LOC | ~330 |
| New feature gates | 8 |
| New lints | 34 |
| New tests | ~180 |

## 10. Key Integration Points

| Subsystem | Key Files | Integration Pattern |
|-----------|-----------|---------------------|
| Pipeline | `pipeline.rs` (5,500+ lines) | `MathAnalysisResults` field + `thread::scope` spawn + collect |
| Lints | `lint.rs` (2,000+ lines) | `LintContext` field + `emit_diagnostic()` |
| Cost-Benefit | `cost_benefit.rs` (50+ variants) | `Optimization` enum variant + cost/benefit function |
| Semirings | `automata/semiring.rs` (1,300+ lines) | New weight type implementing `Semiring` + marker traits |
| WFST | `wfst.rs` (~400 lines) | Extend `PredictionWfst` or new analysis from lattice |
| Decision Tree | `decision_tree.rs` (~3,500 lines) | New `PatternElement` variants or trie enrichment |
| Recovery | `recovery.rs` (~600 lines) | New repair strategies or weighted ranking |
| Prediction | `prediction.rs` (~1,500 lines) | Extended FIRST/FOLLOW with new weight domains |
| Forward-Backward | `forward_backward.rs` | Reuse for probabilistic + training |
| Transducer | `transducer.rs` | `OptimizationPass` trait for new passes |

## 11. Cross-References

- **Plan**: `/home/dylon/.claude/plans/lexical-stargazing-whisper.md`
- **Predicated types design**: [predicated-types.md](../../../docs/design/predicated-types.md)
- **Semiring catalog**: [semiring-catalog.md](semiring-catalog.md)
- **Diagnostics reference**: [diagnostics/README.md](../diagnostics/README.md)
- **Analysis pipeline overview**: [analysis-pipeline-overview.md](analysis-pipeline-overview.md)
- **Optimization pipeline overview**: [optimization-pipeline-overview.md](optimization-pipeline-overview.md)
- **Mathematical analyses**: [mathematical-analyses.md](../../../docs/design/mathematical-analyses.md)

## 12. References

- D'Antoni, L. & Veanes, M. "Minimization of Symbolic Automata" (POPL 2014)
- Droste, M. & Gastin, P. "Weighted Automata and Weighted Logics" (TCS 380, 2007)
- Emerson, E. A. & Jutla, C. S. "Tree Automata, Mu-Calculus and Determinacy" (FOCS 1991)
- Feng, B. & Maletti, A. "Weighted Two-Way Transducers" (CAI 2022; Info. & Computation 293, 2023)
- Kaminski, M. & Francez, N. "Finite-Memory Automata" (TCS 134, 1994)
- Kempe, A. "Weighted Multi-Tape Automata and Transducers for NLP" (2004)
- Kostolanyi, A. & Misun, F. "Alternating Weighted Automata over Commutative Semirings" (TCS 740, 2018)
- Muller, M., Weiss, J. & Lochau, M. "Mapping Cardinality-based Feature Models to Weighted Automata over Featured Multiset Semirings" (2024)
- Zielonka, W. "Infinite Games on Finitely Coloured Graphs with Applications to Automata on Infinite Trees" (TCS 200, 1998)

## 13. Codegen Optimization Status

Four modules have been promoted from `OptimizationStatus::Diagnostic` to
`OptimizationStatus::Auto`, enabling their analysis results to drive codegen
decisions. Two additional modules contribute informational fields.

| Module | Feature Gate | Codegen Status | Optimization ID | Codegen Effect |
|--------|-------------|----------------|-----------------|----------------|
| M1 Symbolic | `symbolic-automata` | **Auto** | SYM01-DCE | Skip dead rules (unsat guards) |
| M2 Buchi | `omega` | Diagnostic | -- | -- |
| M3 Alternating | `alternating` | **Auto** | N06-ISO | Shared dispatch templates |
| M4 VPA | `vpa` | Diagnostic (info) | V05-INFO | Informational: bracket determinism |
| M5 Parity Tree | `parity-tree-automata` | Diagnostic | -- | -- |
| M6 Register | `register-automata` | **Auto** | RA01-SKIP | Skip alpha-equiv (dead binders) |
| M7 Probabilistic | `probabilistic` | **Auto** | PR01-DCE, PR01-WEIGHT | Dead rules + weight blending |
| M8 Multi-Tape | `multi-tape` | Diagnostic (info) | MT01-INFO | Informational: tape independence |
| M9 Multiset | `multiset-automata` | Diagnostic | -- | -- |
| M10 Weighted MSO | `weighted-mso` | Diagnostic | -- | -- |
| M11 Two-Way | `two-way-transducer` | Diagnostic | -- | -- |

See [automata-codegen-optimizations.md](automata-codegen-optimizations.md) for the
full architecture document and [codegen-soundness.md](../theory/optimization/codegen-soundness.md)
for formal correctness proofs.

## 14. Disambiguation, Recovery, and Dispatch Integration

Twelve sprints (A1--A3, B1--B5, C1--C4) integrated advanced automata analysis
results into PraTTaIL's disambiguation, error recovery, and dispatch subsystems.

### Phase A: Leverage Existing REAL Analysis

| Sprint | Integration | Key Effect |
|--------|-------------|------------|
| A1 | VPA nesting depth → recovery cost | Skip actions favored (0.3x) when depth exceeds VPA state count |
| A2 | VPA bracket mismatches → insert penalty | 2.0x penalty on InsertToken for ambiguous bracket tokens |
| A3 | Alternating bisimilar pairs → weight discount | +0.5 tropical penalty on redundant category constructor weights |

### Phase B: Enhance Key Stubs to Real Analysis

Five modules upgraded from trivial stubs to real grammar-driven analysis:

| Sprint | Module | Technique | Impact |
|--------|--------|-----------|--------|
| B1 | Symbolic | FIRST-set guard extraction + overlap/subsumption detection | SYM01-DCE eliminates genuinely dead rules |
| B2 | Buchi | Tarjan SCC on category dependency graph | O01/O02 report real liveness data |
| B3 | Probabilistic | Structure-weighted entropy (1/(1+len)) | PR01-WEIGHT blends non-uniform weights |
| B4 | Register | Binder/capture → Store, NonTerminal → TestEq | RA01-SKIP populates real dead binder data |
| B5 | Multi-Tape | Union-Find connected components on category graph | MT01-INFO populates real independence data |

### Phase C: Cross-Module Integrations

| Sprint | From → To | New `PipelineAnalysis` Field |
|--------|-----------|------------------------------|
| C1 | Symbolic subsumption → disambiguation | `guard_disambiguated_tokens: HashSet<String>` |
| C2 | Buchi accepting SCCs → recovery | `recursive_scc_categories: HashSet<String>` |
| C3 | Probabilistic entropy → beam width | `per_category_entropy: HashMap<String, f64>` |
| C4 | Symbolic subsumption → predicate dispatch | `order_by_specificity()` in `predicate_dispatch.rs` |

**Total**: ~40 new tests, 2,626 tests pass (all-features), zero failures.

### Design and Theory Documentation

| Document | Location | Content |
|----------|----------|---------|
| Integration architecture | [09-automata-disambiguation-integration.md](disambiguation/09-automata-disambiguation-integration.md) | 3-phase cascade (A/B/C), data-flow diagrams, formal transformations, safety invariants |
| Testing strategy | [10-disambiguation-testing-strategy.md](disambiguation/10-disambiguation-testing-strategy.md) | 60 proptest invariants, arbitrary grammar generators, feature gate matrix, edge case catalog |
| Implementation record | [automata-disambiguation-integration.md](../../../docs/design/made/automata-disambiguation-integration.md) | Sprint-by-sprint implementation notes |

### Theory Documents

Formal proofs and analysis supporting the integration:

| Document | Location | Key Results |
|----------|----------|-------------|
| Guard algebra | [symbolic-guard-algebra.md](../theory/disambiguation/symbolic-guard-algebra.md) | Guard overlap implies ambiguity; subsumption-ordered dispatch is sound |
| SCC liveness | [buchi-scc-liveness.md](../theory/disambiguation/buchi-scc-liveness.md) | Tarjan SCC identifies recursive categories; recovery modulation preserves correctness |
| Entropy dispatch | [information-theoretic-dispatch.md](../theory/disambiguation/information-theoretic-dispatch.md) | Shannon entropy drives beam width; structure-weighted entropy outperforms uniform |
| Predicate ordering | [predicate-dispatch-ordering.md](../theory/disambiguation/predicate-dispatch-ordering.md) | Most-specific-first dispatch is safe (Ernst et al. 1998) |
| VPA nesting | [vpa-nesting-recovery.md](../theory/disambiguation/vpa-nesting-recovery.md) | VPA state count bounds well-formed nesting depth |
