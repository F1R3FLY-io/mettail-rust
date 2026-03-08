# Temporal Analysis Diagnostics (L-Category)

**Date:** 2026-03-08
**Source:** `prattail/src/lint.rs` (emission), `prattail/src/ltl.rs` (LTL formulas), `prattail/src/buchi.rs` (Buchi automata)

## 1 Overview

The L-category lints report results from LTL (Linear Temporal Logic) model checking of the grammar's execution traces. LTL properties specify temporal invariants that all infinite parse execution traces must satisfy. The model checking pipeline compiles each LTL formula to a Buchi automaton, constructs the product with the system model (derived from WPDS configurations), and checks for emptiness via SCC analysis.

```
     LTL Property Specifications
               |
               v
   ┌──────────────────────────┐
   │  For each property phi:  │
   │                          │
   │  1. Compile not phi to   │
   │     Buchi automaton      │
   │                          │
   │  2. Product with WPDS    │
   │     system automaton     │
   │                          │
   │  3. SCC emptiness check  │
   └──────────────────────────┘
          |              |
          v              v
    L(prod) = empty  L(prod) != empty
          |              |
          v              v
     Satisfied       Violated
     (counted        (L01 per
      for L02)        violation)
```

All L-category lints require the `ltl` feature gate to be enabled at compile time. Without this feature, the LTL model checking infrastructure is not compiled, and no L-category diagnostics are produced.

## 2 Lint Index

| ID | Severity | Name | Description | Counterexample |
|----|----------|------|-------------|----------------|
| [L01](L01-ltl-violated.md) | Warning | ltl-violated | Buchi product non-empty -- property violated | Lasso-shaped trace (prefix + loop) |
| [L02](L02-ltl-verified.md) | Note | ltl-verified | N LTL properties satisfied | N/A (positive confirmation) |

## 3 Theoretical Background

### 3.1 LTL Formula Grammar

The LTL formulas supported by the model checker follow this grammar:

```
phi ::= true | false | p        (constants and atomic propositions)
      | not phi                  (negation)
      | phi /\ phi               (conjunction)
      | phi \/ phi               (disjunction)
      | phi -> phi               (implication, sugar for not phi \/ psi)
      | X phi                    (next state)
      | F phi                    (eventually, sugar for true U phi)
      | G phi                    (always/globally, sugar for not F not phi)
      | phi U psi                (strong until)
      | phi R psi                (release, dual of until)
      | phi W psi                (weak until)
```

### 3.2 Buchi Acceptance

A Buchi automaton `B = (Q, Sigma, delta, q_0, F)` accepts an infinite word `w = a_0 a_1 a_2 ...` iff there exists a run `rho = q_0 q_1 q_2 ...` such that:

```
For all i >= 0:  q_{i+1} in delta(q_i, a_i)
Inf(rho) intersection F != empty
```

where `Inf(rho)` is the set of states visited infinitely often. The language `L(B)` is exactly the omega-regular languages, which coincide with the LTL-definable properties.

### 3.3 Complexity

| Operation | Complexity |
|-----------|------------|
| LTL to Buchi compilation | 2^O(\|phi\|) states (GPVW tableau) |
| Product construction | O(\|A_sys\| x \|B_neg\|) |
| SCC emptiness check | O(\|V\| + \|E\|) via Tarjan |
| Overall per property | 2^O(\|phi\|) x \|A_sys\| |

## 4 PraTTaIL Integration

LTL properties are specified as part of the mathematical analysis configuration and are checked during the analysis phase of the pipeline. Typical properties for parser grammars include:

- **Balanced delimiters:** `G(open -> F close)` -- every opening delimiter is eventually matched.
- **Error freedom:** `G(not error_state)` -- the parser never enters an error state on valid input.
- **Termination bounds:** `G(reduce -> F idle)` -- every reduction eventually leads to a stable state.
- **Fairness:** `G(F dispatch_cat_A)` -- if category A is reachable, it is dispatched to infinitely often.

## 5 Related Diagnostic Categories

- **W (WFST-Specific):** W13 uses the same WPDS infrastructure for stack-aware reachability.
- **P (Performance):** P06 reports the total analysis phase time, including LTL model checking.
- **D (WPDS):** D14 reports WPDS structural metrics that bound the product automaton size.
