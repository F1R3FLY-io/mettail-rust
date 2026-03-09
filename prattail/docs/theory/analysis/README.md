# PraTTaIL Analysis Module Theory Documentation

This directory contains theoretical documentation for the analysis modules in the
PraTTaIL pipeline. Each document describes the mathematical foundations, core
algorithms, complexity bounds, and PraTTaIL integration points for a single module.

## Complete Module Index

### TRS (Term Rewriting Systems)

| # | Module | Source File | Feature Gate | Lint Codes | Theory Doc |
|---|--------|-------------|-------------|------------|------------|
| 1 | [Confluence](confluence.md) | `confluence.rs` | `trs-analysis` | T01, T02 | Critical pair detection, Knuth-Bendix completion |
| 2 | Termination | `termination.rs` | `trs-analysis` | T03, T04 | Dependency pairs, SCC analysis, polynomial orderings |

### Automata

| # | Module | Source File | Feature Gate | Lint Codes | Theory Doc |
|---|--------|-------------|-------------|------------|------------|
| 3 | [VPA](vpa.md) | `vpa.rs` | `vpa` | V01--V04 | Visibly Pushdown Automata, determinization, closure |
| 4 | [Tree Automata](tree-automaton.md) | `tree_automaton.rs` | `tree-automata` | V03, V04 | Weighted Tree Automata, term recognition |
| 5 | [Alternating](alternating.md) | `alternating.rs` | `alternating` | N05 | Universal branching, game semantics, CTL |
| 6 | Buchi | `buchi.rs` | `omega` | (via L01) | Infinite-word acceptance, parity conditions |
| 7 | [Nominal](nominal.md) | `nominal.rs` | `nominal` | N03, N04 | Orbit-finite sets, name-passing calculi |

### WPDS (Weighted Pushdown Systems)

| # | Module | Source File | Feature Gate | Lint Codes | Theory Doc |
|---|--------|-------------|-------------|------------|------------|
| 8 | WPDS | `wpds.rs` | always-on | W13, W14, W16 | Poststar/prestar, call graph, depth bounds |
| 9 | Verify | `verify.rs` | always-on | S01, S02 | Safety/liveness verification API |
| 10 | [CEGAR](cegar.md) | `cegar.rs` | always-on | S03 | Counterexample-Guided Abstraction Refinement |
| 11 | EWPDS | `ewpds.rs` | `wpds-extended` | S04 | Extended WPDS with merging functions |
| 12 | [ARA](ara.md) | `ara.rs` | `wpds-ara` | S05 | Affine-Relation Analysis, matrix weight domain |

### Mathematical

| # | Module | Source File | Feature Gate | Lint Codes | Theory Doc |
|---|--------|-------------|-------------|------------|------------|
| 13 | [Algebraic](algebraic.md) | `algebraic.rs` | always-on | S06 | Tarjan path expression, interprocedural extension |
| 14 | [Newton](newton.md) | `newton.rs` | `newton` | (internal) | Semiring fixpoint acceleration |
| 15 | Forward-Backward | `forward_backward.rs` | always-on | (internal) | Forward-backward semiring-generic analysis |

### Domain-Specific

| # | Module | Source File | Feature Gate | Lint Codes | Theory Doc |
|---|--------|-------------|-------------|------------|------------|
| 16 | [Petri Nets](petri.md) | `petri.rs` | `petri` | N01, N02 | Petri nets / VASS, coverability, deadlock |
| 17 | Provenance | `provenance.rs` | `provenance` | E01 | How-provenance polynomial tracking |
| 18 | Relational | `relational.rs` | `wpds-relational` | (internal) | Binary relation weight domain |
| 19 | CRA | `cra.rs` | `cra` | E02 | Cost Register Automata, streaming quantitative computation |
| 20 | [Tensor](tensor.md) | `tensor.rs` | `tensor` | (internal) | Tensor product semiring, correlated analysis |

### Meta

| # | Module | Source File | Feature Gate | Lint Codes | Theory Doc |
|---|--------|-------------|-------------|------------|------------|
| 21 | KAT | `kat.rs` | `kat` | K01, K02 | Kleene Algebra with Tests, Hoare logic |
| 22 | [Morphisms](morphism.md) | `morphism.rs` | `morphisms` | M01, M02 | Theory translation, proof transfer |
| 23 | [LTL](ltl.md) | `ltl.rs` | `ltl` | L01, L02 | Linear Temporal Logic, Buchi product |
| -- | [Repair](repair.md) | `repair.rs` | always-on | (internal) | Analysis-driven repair suggestions |

## Cross-References

The following modules have dedicated documentation in other directories:

| Module          | Source File            | Primary Documentation                                                          |
|-----------------|------------------------|--------------------------------------------------------------------------------|
| WPDS            | `wpds.rs`              | [WFST theory](../wfst/), [WPDS design](../../design/wfst/wpds-analysis.md)    |
| EWPDS           | `ewpds.rs`             | [Formal verification](../formal-verification/)                                 |
| Buchi           | `buchi.rs`             | [Buchi-WPDS product](../formal-verification/buchi-wpds-product.md)             |
| KAT             | `kat.rs`               | [KAT soundness](../formal-verification/kat-soundness.md)                       |
| Termination     | `termination.rs`       | [TRS analysis design](../../design/analysis/trs-analysis.md)                   |
| Verify          | `verify.rs`            | [Pushdown verification](../../design/analysis/pushdown-verification.md)        |
| Forward-Backward| `forward_backward.rs`  | [Architecture overview](../../design/architecture-overview.md)                 |
| Repair          | `repair.rs`            | [Meta-level analysis](../../design/analysis/meta-level-analysis.md)            |
| Provenance      | `provenance.rs`        | [Temporal and provenance](../../design/analysis/temporal-and-provenance.md)     |
| CRA             | `cra.rs`               | [Temporal and provenance](../../design/analysis/temporal-and-provenance.md)     |
| Alternating     | `alternating.rs`       | [Automata extensions](../../design/analysis/automata-extensions.md)            |
| Nominal         | `nominal.rs`           | [Concurrency analysis](../../design/analysis/concurrency-analysis.md)          |
| Relational      | `relational.rs`        | [Pushdown verification](../../design/analysis/pushdown-verification.md)        |

## Recommended Reading Order

For readers new to PraTTaIL's analysis infrastructure, the recommended order is:

1. **[Algebraic](algebraic.md)** -- Path expressions form the foundation for all
   weight-based analyses. Understanding `PathExpr<W>` and `evaluate()` is prerequisite.

2. **[CEGAR](cegar.md)** -- The CEGAR loop orchestrates multiple semiring-level
   analyses and demonstrates the abstraction refinement pattern.

3. **[Newton](newton.md)** -- Newton's method accelerates fixpoint computations
   used throughout the pipeline.

4. **[Confluence](confluence.md)** -- Critical pair detection illustrates how
   PraTTaIL models term rewriting from user grammars.

5. **[VPA](vpa.md)** -- VPAs capture the bracket structure of PraTTaIL grammars;
   the determinization algorithm is a key building block for verification.

6. **[LTL](ltl.md)** -- LTL + Buchi compilation demonstrates the temporal
   verification pipeline.

7. **[Petri Nets](petri.md)** -- Petri nets model concurrency in grammars with
   parallel composition operators.

8. **[ARA](ara.md)** -- Affine-relation analysis is the most sophisticated
   weight domain, requiring matrix algebra background.

9. **[Tree Automata](tree-automaton.md)** -- WTA extend the finite-automaton
   framework to tree-structured terms.

10. **[Morphisms](morphism.md)** -- Theory translation builds on all prior
    modules to enable cross-theory reasoning.

11. **[Tensor](tensor.md)** -- The tensor product semiring combines two
    analyses into a single correlated pass.

## Feature Gate Quick Reference

| Feature Gate       | Modules Enabled                                  | Default? |
|--------------------|--------------------------------------------------|----------|
| (always-on)        | algebraic, cegar, verify, wpds, forward-backward, repair | Yes |
| `trs-analysis`     | confluence, termination                          | No       |
| `vpa`              | vpa                                              | No       |
| `tree-automata`    | tree_automaton                                   | No       |
| `alternating`      | alternating                                      | No       |
| `nominal`          | nominal                                          | No       |
| `omega`            | buchi                                            | No       |
| `ltl`              | ltl (requires `omega`)                           | No       |
| `petri`            | petri                                            | No       |
| `cra`              | cra                                              | No       |
| `provenance`       | provenance                                       | No       |
| `wpds-extended`    | ewpds                                            | No       |
| `wpds-ara`         | ara                                              | No       |
| `wpds-relational`  | relational                                       | No       |
| `kat`              | kat                                              | No       |
| `morphisms`        | morphism                                         | No       |
| `newton`           | newton                                           | No       |
| `tensor`           | tensor                                           | No       |
| `proofs`           | proof_output                                     | No       |

Convenience feature groups: `all-analyses`, `all-formal`, `all-features`.

## Conventions

- Unicode symbols: `+` = `oplus`, `*` = `otimes`, `0` = zero, `1` = one
- Semiring operations are written as `w1 oplus w2` and `w1 otimes w2`
- Box-drawing characters are used for diagrams and state machines
- All pseudocode uses imperative style with named variables
- Complexity bounds assume the RAM model unless otherwise noted
- References follow Author (Year) format with full bibliographic details
