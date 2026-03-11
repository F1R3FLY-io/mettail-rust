# Decidability Classification Across the Automata Infrastructure — Cross-Cutting Analysis

## Motivation

Every automata module in MeTTaIL faces the same fundamental question: **which problems can be solved at compile time, which require runtime computation, which are only semi-decidable, and which are undecidable?** The decidability tier classification (T1-T4) provides a uniform framework for answering this question across all 11 modules, enabling the pipeline to make informed decisions about when to analyze, when to defer, and when to warn.

**Core question**: Given a property P expressible in module M over automaton type A, what is the computational complexity of deciding P, and how does the answer change across different automaton types and semiring domains?

**Historical context**: The decidability hierarchy for finite automata has been studied since the pioneering work of Rabin & Scott (1959). For standard finite automata, emptiness, membership, and equivalence are all decidable (PSPACE-complete for equivalence via NFA complementation). As automata gain power — pushdown stacks, registers, multiple tapes, alternation, two-way heads — some problems remain decidable while others cross the undecidability boundary. The key classical results are Rice's theorem (1953) for general computability, the undecidability of Post's correspondence problem (Post, 1946) for multi-tape automata, and the decidability of MSO over finite structures (Buchi, 1960; Elgot, 1961; Trakhtenbrot, 1961).

**Design principle**: The tier system enables **graduated analysis**: the pipeline applies T1 analyses unconditionally at compile time, gates T2 analyses behind cost-benefit checks, applies T3 analyses with explicit depth bounds, and refuses T4 analyses unless the user provides an external proof or assertion.

## The Four-Tier Classification

### Tier T1: Compile-Time Decidable

**Definition**: A problem is T1 if it can be decided in bounded time as a function of the automaton's structural parameters (states, transitions, alphabet size), independent of the input word or external oracle. The decision procedure terminates for all inputs.

**Characteristic complexity**: Polynomial to PSPACE in the size of the automaton. The key property is that the procedure always terminates with a definitive yes/no answer.

**Pipeline treatment**: T1 analyses are run unconditionally during the pipeline's analysis phase. Results are cached in `MathAnalysisResults` and used by downstream consumers (lints, cost-benefit, code generation).

**Examples across modules**:

| Module | Problem | Complexity | Algorithm |
|--------|---------|-----------|-----------|
| M1 Symbolic | SFA emptiness | O(\|Q\|+\|delta\|) + SAT per transition | BFS + satisfiability |
| M1 Symbolic | SFA equivalence | 2x complement + intersection + emptiness | Symmetric difference |
| M2 Buchi | Buchi emptiness | O(\|Q\|+\|delta\|) | Tarjan SCC reachability |
| M3 Alternating | Boolean AFA emptiness | O(2^{\|Q\|}) | Subset construction |
| M4 VPA | VPA emptiness | O(\|Q\|+\|delta\|) | BFS reachability |
| M4 VPA | VPA determinization | O(2^{\|Q\|^2}) | Saturation-based |
| M5 Parity Tree | PATA emptiness | O(\|Q\|^{O(k)}) | Parity game solving |
| M6 Register | RA emptiness (fixed k) | O(\|Q\|^{k+1}) | Configuration graph |
| M7 Probabilistic | Forward/backward | O(\|w\|·\|Q\|²) | Matrix multiplication |
| M8 Multi-tape | K-tape emptiness | O(\|Q\|+\|delta\|) | BFS reachability |
| M9 Multiset | Membership | O(\|w\|·\|Q\|·\|delta\|) | Weight evaluation |
| M10 MSO | Restricted MSO decidability | O(\|phi\|) | Structural classification |
| M11 Two-way | W2T emptiness | O(\|Q\|+\|delta\|) | BFS reachability |

### Tier T2: Runtime Decidable

**Definition**: A problem is T2 if it is decidable but requires information not available at compile time (e.g., runtime input, external database queries, user-provided data). The decision procedure terminates for all inputs when the required information is available.

**Characteristic complexity**: May involve exponential blowup (projection, subset construction) but is guaranteed to terminate.

**Pipeline treatment**: T2 analyses are gated behind cost-benefit checks in `cost_benefit.rs`. If the estimated cost exceeds the benefit threshold, the analysis is deferred to runtime with a generated checker. Diagnostic warnings are emitted for expensive T2 analyses.

**Examples across modules**:

| Module | Problem | Complexity | Why T2 |
|--------|---------|-----------|--------|
| M1 Symbolic | Predicate evaluation on data | O(1) per predicate | Requires runtime data |
| M3 Alternating | Weighted emptiness | O(\|Q\|² · \|delta\|) | Weight computation may need runtime context |
| M4 VPA | Weighted inclusion | O(2^{\|Q\|^2} · \|delta\|) | Exponential but decidable |
| M6 Register | RA evaluation | O(\|w\| · \|Q\| · k!) | Requires input word |
| M7 Probabilistic | Viterbi best path | O(\|w\| · \|Q\|²) | Requires input word |
| M7 Probabilistic | Baum-Welch training | O(\|corpus\| · \|Q\|² · iterations) | Requires training corpus |
| M9 Multiset | Feature interaction | O(exponential in runs) | May require full enumeration |
| M10 MSO | Restricted existential | Exponential projection | Automata construction may blow up |
| M11 Two-way | One-way conversion | O(\|Q\|^{\|Q\|}) | Crossing sequence explosion |

### Tier T3: Semi-Decidable

**Definition**: A problem is T3 if there exists a procedure that will answer "yes" in finite time when the answer is indeed yes, but may run forever when the answer is "no" (or vice versa). Equivalently, the problem is recursively enumerable but not recursive.

**Characteristic**: The procedure can be bounded by a user-specified depth/step limit k, converting it to a bounded decidable check with possible "unknown" outcome.

**Pipeline treatment**: T3 analyses are run with configurable depth bounds (the `--depth-limit` parameter or `PRATTAIL_ANALYSIS_DEPTH` environment variable). Results are three-valued: **yes**, **no** (within bound), or **unknown** (bound exceeded). Diagnostics include the bound used and the residual uncertainty.

**Examples across modules**:

| Module | Problem | Bound Parameter | Semi-Decidable Because |
|--------|---------|----------------|----------------------|
| M3 Alternating | Universal emptiness over infinite semiring | Depth k | Product over positions may diverge |
| M5 Parity Tree | Mu-calculus model checking on infinite trees | Tree depth k | Infinite-depth fixed point |
| M6 Register | Unbounded register RA equivalence | Register count k | Infinite data domain |
| M10 MSO | Full MSO without forall X | Word length k | Unrestricted forall x (non-step body) |

### Tier T4: Undecidable

**Definition**: A problem is T4 if no algorithm can decide it for all inputs. By Rice's theorem, this includes all non-trivial semantic properties of Turing-complete languages.

**Characteristic**: No algorithm terminates with the correct answer on all instances. Specific instances may be decidable, but the general problem is not.

**Pipeline treatment**: T4 analyses are never attempted automatically. The pipeline emits a diagnostic warning ("this property is undecidable in general") and requires the user to provide either:
- An external proof (Rocq certificate)
- A user assertion (`assert_pred`)
- A bounded approximation (downgrade to T3 with explicit bound)

**Examples across modules**:

| Module | Problem | Undecidable Because |
|--------|---------|-------------------|
| M3 Alternating | AFA equivalence over infinite semiring | Reduces to halting problem |
| M4 VPA | VPA equivalence with unbounded stack | Context-free language equivalence |
| M5 Parity Tree | PATA universality | Complement + emptiness over infinite trees |
| M8 Multi-tape | K-tape universality (K >= 2) | Reduces to Post correspondence problem |
| M10 MSO | Full MSO with forall X | Encodes arithmetic over unbounded integers |

## Cross-Module Decidability Matrix

The following matrix summarizes the decidability tier for each property across all 11 modules. Properties are listed in rows; modules in columns. Each cell contains the tier (T1-T4) and a brief complexity note.

### Core Properties

| Property | M1 SFA | M2 Buchi | M3 AWA | M4 VPA | M5 PATA |
|----------|:------:|:--------:|:------:|:------:|:-------:|
| Emptiness | T1 O(n+m) | T1 SCC | T1 2^n | T1 O(n+m) | T1 n^O(k) |
| Membership | T1 O(\|w\|·n) | T1 O(\|w\|·n) | T1 O(\|w\|·2^n) | T1 O(\|w\|·n) | T1 on trees |
| Equivalence | T1 PSPACE | T2 complement | T4 infinite K | T4 CF equiv | T4 |
| Universality | T1 PSPACE | T2 complement | T4 infinite K | T4 | T4 |
| Inclusion | T1 compl+inter | T2 | T2/T4 | T2 weighted | T2 on trees |
| Determinization | T1 2^n | N/A (omega) | N/A (alternating) | T1 2^{n²} | N/A |
| Minimization | T1 n² | T2 | N/A | T2 | N/A |

| Property | M6 RA | M7 Prob | M8 K-Tape | M9 Multiset | M10 MSO | M11 W2T |
|----------|:-----:|:------:|:---------:|:-----------:|:-------:|:-------:|
| Emptiness | T1 n^{k+1} | T1 O(n+m) | T1 O(n+m) | T1 O(n+m) | T1 for RMSO | T1 O(n+m) |
| Membership | T2 O(\|w\|·n·k!) | T1 O(\|w\|·n²) | T1 prod\|w_i\|·n | T1 O(\|w\|·n·m) | T1 for RMSO | T1 O(\|w\|²·n²) |
| Equivalence | T4 unbounded k | T2 | T4 (K>=2) | T2 idem | T1/T4 | T2 |
| Universality | T4 | T4 | T4 (K>=2) | T4 | T1/T4 | T4 |
| Inclusion | T4 | T2 | T4 (K>=2) | T2 | T1/T2 | T2 |

### Analysis Properties

| Property | Tier | Modules | Algorithm |
|----------|:----:|:-------:|-----------|
| Forward algorithm | T1 | M7 | O(\|w\|·n²) matrix multiply |
| Backward algorithm | T1 | M7 | O(\|w\|·n²) matrix multiply |
| Viterbi best path | T2 | M7 | O(\|w\|·n²) requires input |
| Baum-Welch training | T2 | M7 | O(\|corpus\|·n²·iter) requires corpus |
| SCC decomposition | T1 | M2, M11 | O(n+m) Tarjan |
| Deadlock detection | T1 | M11 | O(n+m) Tarjan SCC |
| Cardinality check | T1 | M9 | O(\|w\|·n·m) product automaton |
| Feature interaction | T2 | M9 | Exponential run enumeration |
| Crossing sequence conversion | T2 | M11 | O(n^n) exponential blowup |
| MSO formula classification | T1 | M10 | O(\|phi\|) structural scan |
| Decidability assignment | T1 | M10 | O(\|phi\|) from classification |
| Bisimulation game | T2 | M3 | O(n²·m) game solving |
| Weighted evaluation | T2 | M3, M6, M9 | Requires input word |

## Tier Boundary Analysis

### The T1/T2 Boundary

The critical distinction between T1 and T2 is **input dependence**:
- T1 problems depend only on the automaton's static structure (states, transitions, accepting conditions).
- T2 problems additionally require the input word, a training corpus, or runtime data.

**Structural criterion**: A problem is T1 if it can be answered by examining only the automaton's transition graph without reference to any specific input. Emptiness, state reachability, and structural properties (determinism, minimality) are inherently T1. Membership, evaluation, and training are inherently T2 because they require an input.

**Exception**: Some T2 problems can be "lifted" to T1 by approximation. For example, probabilistic selectivity estimation (M7) is T2 for a specific input but T1 for the entropy bound (which depends only on the automaton's structure).

### The T2/T3 Boundary

The critical distinction between T2 and T3 is **termination guarantee**:
- T2 problems always terminate (the search space is finite).
- T3 problems may not terminate (the search space is potentially infinite or the procedure may diverge).

**Structural criterion**: A problem becomes T3 when it involves quantification over an infinite domain or an unbounded iteration. Register automata equivalence for unbounded register count is T3 because the data domain is infinite. Full MSO with unrestricted forall x is T3 because the product over positions may not define a recognizable series.

### The T3/T4 Boundary

The critical distinction between T3 and T4 is **asymmetric decidability**:
- T3 problems are semi-decidable: "yes" instances can be confirmed in finite time.
- T4 problems are not even semi-decidable: there is no procedure that correctly identifies all "yes" instances.

**Structural criterion**: A problem is T4 when it can encode the halting problem or an equivalent undecidable problem. Multi-tape universality for K >= 2 is T4 because it can encode Post's correspondence problem. Full MSO with forall X over infinite semirings is T4 because it can encode unbounded arithmetic.

## Semiring Influence on Decidability

The choice of semiring can shift a problem's decidability tier. The following analysis shows how:

| Semiring | Properties | Effect on Decidability |
|----------|------------|----------------------|
| Boolean (B, or, and, 0, 1) | Finite, idempotent | Most favorable: classical algorithms apply directly |
| Tropical (R+inf, min, +, inf, 0) | Infinite but idempotent | Shortest-path algorithms converge; equivalence decidable via canonical forms |
| Counting (N, +, *, 0, 1) | Infinite, not idempotent | Ambiguity counting is PSPACE; some equivalences become harder |
| Log (R, logadd, +, -inf, 0) | Infinite, not idempotent | Numerical stability issues but algorithms terminate |
| Entropy | Infinite, not idempotent | Fixed-point computations may not converge without bounds |
| Multiset (N0^F, max, +) | Infinite, idempotent | Per-feature analysis adds O(\|F\|) factor; core decidability preserved |
| Amplitude (C, +, *, 0, 1) | Infinite, not idempotent | Quantum CTMC; convergence requires norm bounds |

**Key insight**: Idempotent semirings (Boolean, Tropical, Multiset) preserve T1/T2 classification for most problems because Kleene iteration converges. Non-idempotent semirings (Counting, Log, Entropy) may shift problems from T1 to T2 when fixed-point computation requires runtime bounds.

## Implementation in MeTTaIL

### DecidabilityTier Enum

The tier classification is implemented in `prattail/src/symbolic.rs`:

```
enum DecidabilityTier {
    CompileTimeDecidable,    // T1
    RuntimeDecidable,        // T2
    SemiDecidable,           // T3
    Undecidable,             // T4
}
```

### Classification Functions

Each module provides an `analyze_from_bundle()` function that returns analysis results including decidability information. The weighted MSO module provides the most explicit classification:

- `classify_formula(phi)` -> `MsoFormulaClass` (structural fragment)
- `check_decidability(phi)` -> `DecidabilityTier` (tier assignment)
- `analyze_formula(phi)` -> `MsoAnalysis` (comprehensive result)

### Pipeline Integration

The pipeline uses tier information to gate analyses:

1. **T1 analyses**: Run in the `thread::scope` parallel analysis phase.
2. **T2 analyses**: Gated by `Optimization` enum variants in `cost_benefit.rs`.
3. **T3 analyses**: Run with user-configurable depth bounds.
4. **T4 analyses**: Never run automatically; diagnostic warnings emitted.

### Lint Integration

Lint rules reference decidability tiers to set severity:

- T1 lints: errors or warnings (the property is statically checkable).
- T2 lints: notes (the property requires runtime checking).
- T3 lints: info (the property is partially checkable with bounds).
- T4 lints: never fire automatically (would be unsound).

## Connections to Classical Results

| Classical Result | Year | Relevance |
|-----------------|------|-----------|
| Rice's Theorem | 1953 | All non-trivial semantic properties of RE languages are T4 |
| Rabin-Scott Theorem | 1959 | NFA emptiness/equivalence are T1 (foundation for all T1 results) |
| Buchi's Theorem | 1960 | MSO over omega-words <=> omega-regular (T1 for Boolean) |
| Buchi-Elgot-Trakhtenbrot | 1960-61 | MSO over finite words <=> regular (T1) |
| Post Correspondence Problem | 1946 | Multi-tape universality K>=2 is T4 |
| Shepherdson's Conversion | 1959 | Two-way -> one-way is T2 (exponential but decidable) |
| Alur-Madhusudan VPA | 2004 | VPA emptiness/determinization are T1 |
| Droste-Gastin Theorem | 2007 | Restricted weighted MSO <=> recognizable (T1) |
| Kaminski-Francez RA | 1994 | RA emptiness is T1 for fixed registers |

## Bibliography

1. Rice, H.G. (1953). "Classes of Recursively Enumerable Sets and Their Decision Problems." *Transactions of the American Mathematical Society*, 74(2), pp. 358-366.

2. Rabin, M.O. & Scott, D. (1959). "Finite Automata and Their Decision Problems." *IBM Journal of Research and Development*, 3(2), pp. 114-125.

3. Buchi, J.R. (1960). "Weak Second-Order Arithmetic and Finite Automata." *Mathematical Logic Quarterly*, 6(1-6), pp. 66-92.

4. Elgot, C.C. (1961). "Decision Problems of Finite Automata Design and Related Arithmetics." *Transactions of the American Mathematical Society*, 98(1), pp. 21-51.

5. Trakhtenbrot, B.A. (1961). "Finite automata and the logic of one-place predicates." *Doklady Akademii Nauk SSSR*, 140, pp. 326-329.

6. Post, E.L. (1946). "A Variant of a Recursively Unsolvable Problem." *Bulletin of the American Mathematical Society*, 52, pp. 264-268.

7. Droste, M. & Gastin, P. (2007). "Weighted automata and weighted logics." *Theoretical Computer Science*, 380(1-2), pp. 69-86.

8. Alur, R. & Madhusudan, P. (2004). "Visibly Pushdown Languages." In *STOC '04*, pp. 202-211. ACM.

9. Kaminski, M. & Francez, N. (1994). "Finite-Memory Automata." *Theoretical Computer Science*, 134(2), pp. 329-363.

10. Mohri, M. (2009). "Weighted Automata Algorithms." In *Handbook of Weighted Automata*, pp. 213-254. Springer.

11. Shepherdson, J.C. (1959). "The Reduction of Two-Way Automata to One-Way Automata." *IBM Journal of Research and Development*, 3(2), pp. 198-200.
