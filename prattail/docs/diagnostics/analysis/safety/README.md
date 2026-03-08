# Safety Analysis Diagnostics (S-Category)

**Source:** `prattail/src/lint.rs` (emission), `prattail/src/verify.rs` (S01/S02),
`prattail/src/cegar.rs` (S03), `prattail/src/ewpds.rs` (S04),
`prattail/src/ara.rs` (S05), `prattail/src/algebraic.rs` (S06)

## Overview

The S-category lints report on the safety, correctness, and structural properties
of the grammar's inter-procedural control flow as modeled by weighted pushdown
systems (WPDS) and their extensions. These diagnostics range from actionable
warnings (a safety property is violated) to informational notes (analysis
summaries and structural observations).

The analysis pipeline follows a layered architecture:

```
  ┌───────────────────────────────────────────────────────────────┐
  │                     Grammar Specification                     │
  └───────────────────────────────┬───────────────────────────────┘
                                  │
                                  v
  ┌───────────────────────────────────────────────────────────────┐
  │  WPDS Construction (wpds.rs)                                  │
  │  Categories --> control states, rules --> transition rules    │
  │  Cross-category calls --> push/pop transitions                │
  └──────┬──────────────┬─────────────┬──────────────┬────────────┘
         │              │             │              │
         v              v             v              v
  ┌────────────┐ ┌────────────┐ ┌──────────┐ ┌────────────────┐
  │  prestar   │ │   CEGAR    │ │  EWPDS   │ │   Algebraic    │
  │ (verify.rs)│ │ (cegar.rs) │ │(ewpds.rs)│ │ (algebraic.rs) │
  └─────┬──────┘ └─────┬──────┘ └────┬─────┘ └──────┬─────────┘
        │              │             │              │
        v              v             v              v
  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────────┐
  │ S01/S02  │  │   S03    │  │   S04    │  │     S06      │
  │ safety   │  │  CEGAR   │  │  merge   │  │   Tarjan     │
  │ verdict  │  │  report  │  │  sites   │  │   summary    │
  └──────────┘  └──────────┘  └──────────┘  └──────────────┘
                                  │
                                  v
                           ┌──────────┐
                           │   S05    │  (requires wpds-ara)
                           │   ARA    │
                           │invariants│
                           └──────────┘
```

## Lint Index

| ID | Name | Severity | Feature Gate | Description |
|----|------|----------|--------------|-------------|
| [S01](S01-safety-violation.md) | safety-violation | Warning | always-on | Bad state reachable via WPDS prestar |
| [S02](S02-safety-verified.md) | safety-verified | Note | always-on | No bad states reachable -- safety verified |
| [S03](S03-cegar-refinement.md) | cegar-refinement | Note | always-on | CEGAR loop summary: steps and verdict |
| [S04](S04-ewpds-merge-site.md) | ewpds-merge-site | Note | `wpds-extended` | EWPDS merge function sites identified |
| [S05](S05-ara-invariant.md) | ara-invariant | Note | `wpds-ara` | ARA weight domain dimension and invariants |
| [S06](S06-algebraic-summary.md) | algebraic-summary | Note | always-on | Tarjan path expression SCC/expression counts |

## Severity Distribution

- **Warning (1):** S01 -- requires grammar author review and corrective action.
- **Note (5):** S02-S06 -- informational, providing analysis summaries and
  structural observations that support understanding of the grammar's properties.

## Feature Gates

Three of the six lints are always-on (S01, S02, S03, S06). Two require
specific feature gates:

| Feature | Lints | Description |
|---------|-------|-------------|
| `wpds-extended` | S04 | Extended WPDS with merge functions |
| `wpds-ara` | S05 | Algebraic program analysis with recurrences |

## Theoretical Background

The safety analysis is grounded in the theory of weighted pushdown systems
(Reps, Schwoon, Jha & Melski, 2005). Key concepts:

- **P-automaton:** A finite automaton that accepts a set of WPDS configurations.
  Each configuration is a pair (p, w) where p is a control state and w is a
  stack word.

- **Prestar:** The backward reachability algorithm that saturates a P-automaton
  to include all configurations from which a target set is reachable.

- **EWPDS:** An extension where return transitions use ternary merge functions
  instead of binary semiring multiplication, enabling more precise modeling of
  call/return interactions.

- **ARA:** An algebraic framework that lifts WPDS weights to affine relations,
  enabling automatic discovery of numerical invariants.

- **CEGAR:** An iterative refinement technique that uses increasingly precise
  abstract domains to verify or refute safety properties.

- **Tarjan path expressions:** Regular expressions over the semiring algebra
  that summarize all paths within strongly connected components of the call
  graph.

## Related Diagnostic Categories

- **W (WFST-Specific):** W01, W13-W14, W16 -- WFST and WPDS rule-level diagnostics
- **D (Decision Tree):** D14-D15 -- WPDS complexity and witness trace reports
- **N (Concurrency):** N01-N05 -- concurrency analysis (Petri nets, nominal, alternating)
- **COMP (Composition):** COMP-08 -- grammar refactoring suggestions from WPDS analysis
