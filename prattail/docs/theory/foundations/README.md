# Mathematical Foundations

This directory provides formal mathematical grounding for PraTTaIL from seven
disciplines. Each document is self-contained: essential definitions, one or more
key theorems with complete proofs, and concrete connections to PraTTaIL source
code.

---

## Dependency Diagram

```
                    ┌─────────────────────┐
                    │  01  Order Theory   │
                    │  (posets, lattices, │
                    │   fixed-points)     │
                    └──┬──┬──┬──┬──┬──┬───┘
                       │  │  │  │  │  │
          ┌────────────┘  │  │  │  │  └────────────┐
          │     ┌─────────┘  │  │  └─────────┐     │
          ▼     ▼            │  │            ▼     ▼
  ┌──────────┐ ┌──────────┐  │  │  ┌──────────┐ ┌──────────┐
  │ 02       │ │ 03       │  │  │  │ 06       │ │ 07       │
  │ Automata │ │ Language │  │  │  │ Optim.   │ │ Machine  │
  │ Theory   │ │ Theory   │  │  │  │ Theory   │ │ Learning │
  └────┬─────┘ └────┬─────┘  │  │  └────┬─────┘ └──────────┘
       │            │        │  │       │            ▲
       │        ┌───┘        │  │       │            │
       ▼        ▼            │  │       └────────────┘
  ┌──────────┐ ┌──────────┐  │  │
  │ 04       │ │ 05       │  │  │
  │ Compiler │ │ Parsing  │◄─┘  │
  │ Theory   │ │ Algebra  │◄────┘
  └──────────┘ └──────────┘
```

**01 — Order Theory** is foundational. All other documents reference it for
partial orders, lattice definitions, and fixed-point theorems.

---

## Reading Order by Audience

**Mathematician / type theorist:**
01 → 05 → 03 → 06 → 07

**Compiler engineer:**
01 → 02 → 04 → 05 → 03

**ML / NLP researcher:**
01 → 06 → 07 → 02 → 05

**Quick orientation (any background):**
01 §§ 1–3 → 02 § 2 → 06 § 2 → done

---

## Master Correspondence Table

| PraTTaIL Structure                       | Source File                    | Concept                                                | Document                                                          |
|------------------------------------------|--------------------------------|--------------------------------------------------------|-------------------------------------------------------------------|
| `BooleanWeight`                          | `semiring.rs:301`              | Boolean algebra (bounded distributive lattice)         | [01](01-order-theory.md) § 4                                      |
| `ComplexityWeight`                       | `semiring.rs:781`              | Bottleneck semiring / minimax                          | [01](01-order-theory.md) § 4, [06](06-optimization-theory.md) § 4 |
| `ContextWeight`                          | `semiring.rs:643`              | Power-set lattice 𝒫({0..127})                          | [01](01-order-theory.md) § 4                                      |
| `TropicalWeight`                         | `semiring.rs:69`               | Idempotent semiring → semilattice                      | [01](01-order-theory.md) § 3                                      |
| `CountingWeight`                         | `semiring.rs:219`              | Non-idempotent (ℕ, +, ×)                               | [01](01-order-theory.md) § 3                                      |
| `LogWeight`                              | `semiring.rs:916`              | Neg-log-probability, exponential family                | [07](07-machine-learning.md) §§ 1–2                               |
| `EntropyWeight`                          | `semiring.rs:1120`             | Shannon entropy via expectation semiring               | [07](07-machine-learning.md) § 3                                  |
| `ProductWeight`                          | `semiring.rs:513`              | Lexicographic multi-objective                          | [06](06-optimization-theory.md) § 5                               |
| `NbestWeight`                            | `semiring.rs:1418`             | N-best path tracking                                   | [06](06-optimization-theory.md) § 2                               |
| `compute_first_sets()`                   | `prediction.rs:213`            | Kleene fixed-point on complete lattice                 | [01](01-order-theory.md) § 5, [05](05-parsing-algebra.md) § 1     |
| `compute_follow_sets_from_inputs()`      | `prediction.rs:288`            | Kleene fixed-point (FOLLOW)                            | [05](05-parsing-algebra.md) § 1                                   |
| `minimize_dfa()`                         | `automata/minimize.rs`         | Myhill-Nerode congruence on Σ*                         | [02](02-automata-theory.md) § 2                                   |
| NFA→DFA subset construction              | `automata/subset.rs`           | Determinization (powerset construction)                | [02](02-automata-theory.md) § 3                                   |
| Pratt binding power                      | `pratt.rs`                     | Operator-precedence grammar (Floyd 1963)               | [04](04-compiler-theory.md) § 3                                   |
| Trampoline + `Frame_Cat`                 | `trampoline.rs`                | Defunctionalized CPS                                   | [04](04-compiler-theory.md) § 4                                   |
| `TokenLattice<T,S,W>`                    | `lattice.rs:246`               | Weighted DAG for semiring DP                           | [06](06-optimization-theory.md) § 2                               |
| `viterbi_generic`                        | `lattice.rs:490`               | Viterbi as semiring shortest-path                      | [06](06-optimization-theory.md) § 2                               |
| `viterbi_best_path_beam()`               | `lattice.rs:377`               | Beam search as bounded A*                              | [06](06-optimization-theory.md) § 3                               |
| `forward_scores()` / `backward_scores()` | `forward_backward.rs`          | Expectation on exponential families                    | [07](07-machine-learning.md) § 2                                  |
| `predict_with_confidence()`              | `wfst.rs`                      | Information-theoretic beam width                       | [07](07-machine-learning.md) § 4                                  |
| Language `extends`/`includes`/`compose`  | macros                         | CFL closure properties                                 | [03](03-language-theory.md) § 1                                   |
| `CancellationPair` detection             | `pattern.rs`                   | Term rewriting / Church-Rosser                         | [03](03-language-theory.md) § 3                                   |
| Ascent `logic {}` blocks                 | macros                         | Datalog = fixed-point over relation lattice            | [01](01-order-theory.md) § 5, [04](04-compiler-theory.md) § 2     |
| Multi-semiring evaluation                | `pipeline.rs`, `lattice.rs`    | Same topology, different semiring → different analysis | [05](05-parsing-algebra.md) § 3                                   |
| DFA lexer                                | `automata/nfa.rs`, `subset.rs` | Chomsky Type-3 recognizer                              | [02](02-automata-theory.md) § 1                                   |
| Two-phase lex → parse                    | `codegen.rs`                   | Bar-Hillel: CFL ∩ Regular = CFL                        | [03](03-language-theory.md) § 2                                   |

---

## Document Index

| #                               | Title                     | Lines | Key Theorems                                                                                                    |
|---------------------------------|---------------------------|-------|-----------------------------------------------------------------------------------------------------------------|
| [01](01-order-theory.md)        | Order Theory and Lattices | ~400  | Idempotent semiring ↔ semilattice; BooleanWeight/ContextWeight are Boolean algebras; Kleene fixed-point theorem |
| [02](02-automata-theory.md)     | Classical Automata Theory | ~250  | Myhill-Nerode theorem; weighted automata over semirings                                                         |
| [03](03-language-theory.md)     | Formal Language Theory    | ~250  | Bar-Hillel (CFL ∩ Reg = CFL); cancellation pair termination                                                     |
| [04](04-compiler-theory.md)     | Compiler Theory           | ~250  | Pratt-Floyd correspondence (OPG ↔ binding power); Datalog fixed-point semantics                                 |
| [05](05-parsing-algebra.md)     | Parsing Algebra           | ~300  | FIRST sets via Kleene iteration; semiring homomorphism preservation                                             |
| [06](06-optimization-theory.md) | Optimization Theory       | ~300  | Viterbi correctness (induction on topo order); beam as bounded A*; minimax bottleneck                           |
| [07](07-machine-learning.md)    | Machine Learning Theory   | ~300  | ∇A(θ) = E[φ(x)]; single-pass entropy via expectation semiring; entropy lower-bounds support                     |

---

## References (Collected)

References are listed per-document. The most frequently cited works across the
series:

- Davey, B. A. & Priestley, H. A. (2002). *Introduction to Lattices and Order*. Cambridge.
- Droste, M., Kuich, W., & Vogler, H. (2009). *Handbook of Weighted Automata*. Springer.
- Mohri, M. (2002). "Semiring frameworks and algorithms for shortest-distance problems." *JALC*, 7(3), 321–350.
- Hopcroft, J. E. & Ullman, J. D. (1979). *Introduction to Automata Theory, Languages, and Computation*. Addison-Wesley.
- Pratt, V. R. (1973). "Top down operator precedence." *POPL '73*, 41–51.
- Li, Z. & Eisner, J. (2009). "First- and Second-Order Expectation Semirings." *EMNLP*, 40–51.
