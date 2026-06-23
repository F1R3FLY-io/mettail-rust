# Requirements Traceability

Last updated: 2026-06-22

This page maps each documentation requirement for the semantic-predicate substrate
to the document that satisfies it, so a reviewer can confirm coverage without
reading the whole suite. It also records the consistency conditions that
[`validate.sh`](validate.sh) enforces.

## Coverage map

| Requirement | Satisfied by |
|---|---|
| Define every symbol, acronym, and term before use | [01 — Concepts and Glossary](01-concepts-and-glossary.md) |
| Document the effective Boolean algebra: definition, trait, decision procedures, minterms, instances | [02 — Effective Boolean Algebra](02-effective-boolean-algebra.md) |
| Document symbolic finite automata: recognition, emptiness, closure, determinization, equivalence, guard analysis | [03 — Symbolic Automata (SFA)](03-symbolic-automata-sfa.md) |
| Document symbolic finite/tree transducers: transduction, output-term algebra, composition, pre/post-image, functionality | [04 — Symbolic Transducers (SFT / STFT)](04-symbolic-transducers-sft-stft.md) |
| Document the algebra tower, three-valued satisfiability, decidability tiers, and the closure family | [05 — Algebra Pyramid and Decidability](05-algebra-pyramid-and-decidability.md) |
| Document the supported guard syntax and propose syntax for the unsupported features | [06 — Guard Syntax and Extensions](06-guard-syntax-and-extensions.md) |
| Document the end-to-end `language!` → classification → fail-closed gate path | [07 — Language-to-Rholang Integration](07-language-to-rholang-integration.md) |
| Answer how a semantic predicate is enforced at run time (the COMM-enforcement crux) | [08 — Runtime COMM Enforcement](08-runtime-comm-enforcement.md) |
| Answer how the predicate algebra aligns with the OSLF design (the composition crux) | [09 — OSLF Composition](09-oslf-composition.md) |
| Provide the mechanized-proof matrix, zero-admission gate, and runtime tests | [10 — Formal Verification and Tests](10-formal-verification-and-tests.md) |
| Provide a concrete end-to-end worked example | [11 — Worked Example: GuardedRho](11-worked-example.md) |
| Argue why Heyting/intuitionistic logic governs behavioral constraints, how bisimulation makes them well-defined, and how it completes Boolean and aligns with OSLF | [12 — Heyting Behavioral Logic](12-heyting-behavioral-logic.md) |
| Document the LogicT constraint-theory engine and its integration: quantified-predicate evaluation, the theory-to-EBA bridge, theory combination, and predicated-type enforcement | [13 — Constraint-Theory Engine](13-constraint-theory-engine.md) |
| Document thoroughly and precisely how existential and universal quantification are modeled: the three realizations, the domain model, the `∀≡¬∃¬` duality, decidability, lowering, and a worked example | [14 — Quantification](14-quantification.md) |
| Document the modal μ-calculus of the behavioral Heyting algebra: syntax, Knaster–Tarski fixpoint semantics, how a process is concretized as an LTS to be predicated against, the model-checking algorithm and its exactness, and the CTL encoding — all proved | [15 — Modal μ-Calculus](15-mu-calculus.md) |
| Provide citations with DOIs and a repository-local artifact index | [References](references.md) |
| Provide diagrams of the best type with the best actors per concept | `figures/` (see the diagramming policy in the [README](README.md#diagramming-choices)) |
| Provide a one-page decision brief | [00 — Executive Brief](00-executive-brief.md) |

## Claim kinds

The suite makes four kinds of claim; each is traceable to a different kind of
evidence so a reviewer can apply the right scrutiny:

| Claim kind | Where stated | How to verify |
|---|---|---|
| architectural (what owns what; classify-only boundary) | [07](07-language-to-rholang-integration.md), [08](08-runtime-comm-enforcement.md) | read the named Rust modules in [References](references.md) |
| algebraic (the EBA laws, closure, tower, transducer algebra) | [02](02-effective-boolean-algebra.md)–[05](05-algebra-pyramid-and-decidability.md) | the zero-admission Rocq theories in [10](10-formal-verification-and-tests.md) |
| run-time (guard atomicity, enforcement mechanism) | [08](08-runtime-comm-enforcement.md) | the host oracle tests in [10 §4](10-formal-verification-and-tests.md) |
| syntactic (what parses today; what is proposed) | [06](06-guard-syntax-and-extensions.md) | the parser entry points named per construct |

## Consistency conditions (enforced by `validate.sh`)

| Condition | Check |
|---|---|
| no draft / incompleteness markers in the suite | the marker scan (the proof keywords `Axiom`/`Conjecture`/`Admitted.` are exempt only in [10](10-formal-verification-and-tests.md), which must name them to explain the zero-admission gate) |
| every mathematical expression is in backticks | the math-symbol literal scan |
| every relative link and anchor resolves | the Markdown link check |
| every figure reference has a rendered, valid, non-escaped SVG asset | the PlantUML figure-asset check |
| every repository-local path in [References](references.md) resolves | the bibliography local-path check |
| every external DOI / link resolves (with `--online`) | the external-link check |
| no trailing-whitespace or conflict markers | `git diff --check` |

## Cross-suite relationship

This suite is the theory-of-guards layer between the language definition and the
rewrite/execution backends. It is consumed by, and consistent with, the two
companion suites:

- [Dovetail](../dovetail/README.md) consumes the covered guarded rewrite rules.
- [Rho-Native Integration](../rho-native-integration/README.md) lowers a covered
  language to `rhoapi::Par` and enforces the surviving guard at run time. Its
  `04-rho-native-dataflow-lowering.md` documents the same obligation/disposition
  matrix from the lowering side; this suite documents it from the algebra side.
