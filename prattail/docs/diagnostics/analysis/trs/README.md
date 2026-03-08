# TRS Analysis Diagnostics (T-Category)

**Source:** `prattail/src/confluence.rs`, `prattail/src/termination.rs`, `prattail/src/lint.rs`
**Feature Gate:** `trs-analysis`

## 1 Overview

The T-category lints report on the **term rewriting system** (TRS) properties of
a PraTTaIL grammar. A TRS is a set of directed equations (rewrite rules)
l -> r that transform terms. Two fundamental properties determine whether the
TRS behaves predictably:

- **Confluence** (Church-Rosser property): rewriting produces the same result
  regardless of which rule is applied first. Checked via the Knuth-Bendix
  critical pair theorem -- every overlapping rule pair must produce joinable
  reducts.

- **Termination** (strong normalization): every reduction sequence is finite.
  Checked via dependency pair analysis -- every strongly connected component in
  the dependency graph must admit a decreasing well-founded ordering.

A TRS that is both confluent and terminating is called **convergent**
(canonical). In a convergent system, every term has a unique normal form that
can be computed by any reduction strategy.

```
                    TRS Properties
  ┌──────────────────────────────────────────────┐
  │                                              │
  │   Confluent?         Terminating?            │
  │   ┌────────┐         ┌───────────┐           │
  │   │ T01/T02│         │  T03/T04  │           │
  │   └───┬────┘         └─────┬─────┘           │
  │       │                    │                 │
  │       v                    v                 │
  │   ┌────────┐         ┌───────────┐           │
  │   │  yes?  │         │   yes?    │           │
  │   │ -> T02 │         │  -> T04   │           │
  │   │  no?   │         │   no?     │           │
  │   │ -> T01 │         │  -> T03   │           │
  │   └────────┘         └───────────┘           │
  │       │                    │                 │
  │       └────────┬───────────┘                 │
  │                v                             │
  │        ┌──────────────┐                      │
  │        │ T02 + T04 =  │                      │
  │        │  Convergent  │                      │
  │        └──────────────┘                      │
  └──────────────────────────────────────────────┘
```

## 2 Lint Index

| ID | Severity | Name | Description |
|----|----------|------|-------------|
| [T01](T01-non-joinable-critical-pair.md) | Warning | non-joinable-critical-pair | Critical pair (rules i, j) fails to join -- confluence violation |
| [T02](T02-confluence-verified.md) | Note | confluence-verified | All N critical pairs joinable -- system is confluent |
| [T03](T03-non-terminating-cycle.md) | Warning | non-terminating-cycle | Dependency graph SCC lacks decreasing measure -- potential non-termination |
| [T04](T04-termination-verified.md) | Note | termination-verified | All SCCs have decreasing measures -- system terminates |

## 3 Activation Status

All T-category lints require the `trs-analysis` feature gate:

```toml
[dependencies]
prattail = { version = "...", features = ["trs-analysis"] }
```

When the feature is enabled, the pipeline runs confluence and termination
analysis after rule extraction. The analysis results are stored in the lint
context as `confluence_result: Option<&ConfluenceAnalysis>` and
`termination_result: Option<&TerminationResult>`.

Lints fire only when the corresponding analysis result is `Some(...)`:

| Lint | Required context field | Fires when |
|------|----------------------|------------|
| T01 | `confluence_result` | `JoinabilityResult::NotJoinable` for any critical pair |
| T02 | `confluence_result` | `is_confluent == true` |
| T03 | `termination_result` | `TerminationResult::PotentiallyNonTerminating { ... }` |
| T04 | `termination_result` | `TerminationResult::Terminating` |

## 4 Architecture

The T-category analysis is split across three source files:

### confluence.rs

Implements the Knuth-Bendix critical pair computation:

1. **Unification:** For each pair of rules (l₁ -> r₁, l₂ -> r₂), the analysis
   attempts to unify l₁ with every non-variable subterm of l₂ using a most
   general unifier (MGU) algorithm.

2. **Critical pair generation:** When unification succeeds at position p with
   MGU sigma, the critical pair langle r₁sigma, l₂[r₂]_p sigma rangle is
   recorded as a `CriticalPair` struct.

3. **Joinability checking:** Each critical pair's two reducts are normalized
   (reduced to normal form within a bounded number of steps). If both sides
   reach the same term, the pair is `Joinable`; otherwise `NotJoinable`.

Key types: `CriticalPair`, `JoinabilityResult`, `ConfluenceAnalysis`.

### termination.rs

Implements dependency pair analysis:

1. **Dependency graph construction:** For each rule l -> r, the defined symbols
   in r that also appear as root symbols in some LHS form dependency pairs. The
   graph connects pairs that can chain.

2. **SCC decomposition:** Tarjan's algorithm decomposes the dependency graph
   into strongly connected components.

3. **Measure verification:** Each non-trivial SCC is checked for a decreasing
   ordering (term size, polynomial interpretation, or other well-founded
   measure).

Key types: `TerminationResult`, `DependencyPairScc`.

### lint.rs

Contains the four lint functions (`lint_t01_*` through `lint_t04_*`) that read
the analysis results from `LintContext` and emit `LintDiagnostic` structs.

## 5 Mutual Exclusivity

The T-category lints exhibit pairwise mutual exclusivity at the system level:

- **T01 and T02:** T02 fires only when `is_confluent` is true, which requires
  zero non-joinable pairs. T01 fires for each non-joinable pair. They cannot
  co-occur.

- **T03 and T04:** T04 fires only for `TerminationResult::Terminating`. T03
  fires only for `PotentiallyNonTerminating`. They cannot co-occur.

- **T01 and T03/T04, T02 and T03/T04:** These are independent. A TRS can be
  confluent but non-terminating (T02 + T03), terminating but non-confluent
  (T04 + T01), or any combination.

## 6 Related Diagnostic Categories

- **G (Grammar Structure):** G01--G10 -- Structural grammar lints that may
  affect rewriting rule formation.
- **W (WFST-Specific):** W01--W16 -- WFST prediction lints. Dead rules (W01)
  may correlate with unreachable rewrite rules.
- **V (Automata):** [V01--V04](../automata/README.md) -- VPA and WTA analysis
  lints. Orthogonal to TRS analysis but part of the same mathematical analysis
  framework.
- **S (Safety):** S01--S06 -- Safety verification lints. May depend on TRS
  properties (e.g., a confluent TRS ensures deterministic safety checking).
