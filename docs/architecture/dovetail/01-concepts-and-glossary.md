# Concepts and Glossary

This page defines Dovetail terms before they appear in formulas or algorithms.

## Core Terms

| Term | Definition |
|---|---|
| MeTTaIL | A language modeling system that defines syntax and rewrite semantics for object languages. |
| Dovetail | The standalone MeTTaIL rewrite engine crate at `dovetail/`. |
| rewrite rule | A data value with a left-hand pattern and right-hand pattern. |
| equality saturation | Iterative growth of an equality graph until no new equalities are found or a bound stops the run. |
| e-graph | A graph of equivalence classes and expression nodes. |
| e-class | An equivalence class of terms, identified by `EClassId`. |
| e-node | A labeled operator with zero or more child e-classes. |
| congruence closure | The rule that if children are equal, parent expressions with the same operator are equal. |
| exact key | A byte-stream identity where equality is byte equality, represented by `ContentKey`. |
| semantic hash | Dovetail's name for exact content serialization; despite the name, it is not a finite hash. |
| weight | A semiring value used to order derivations. |
| semiring | Algebra with `⊕`, `⊗`, `0̄`, and `1̄`. |
| weighted tree automaton | A tree automaton whose transitions carry weights. |
| DFTA | Deterministic finite tree automaton; Dovetail views e-classes as states and e-nodes as transitions. |
| inside weight | The aggregate weight of all derivations rooted at an e-class. |
| SCC | Strongly connected component in the e-class dependency graph. |
| extraction | Enumeration of derivation trees from an e-class. |
| derivation | A chosen e-node plus one derivation for each child e-class. |
| report | A runtime-facing, proof-preserving artifact built from checked extraction output. |
| report consumer | An adapter or oracle that reads a report without depending on Dovetail internals. |
| term record | A unique derivation node recorded once in a report under its exact `ContentKey`. |
| derivation edge | A report edge from parent key to child key, preserving child order and repeated child uses. |
| cycle cut | A recursion guard that prevents infinite enumeration through a back-edge. |
| completeness | Terminal metadata saying whether extracted output is exhaustive or bounded by a cycle cut. |
| tuple-space seam | Generic `TupleSpace` and `Match` traits used to model rendezvous without depending on RSpace. |

## Symbols

| Symbol | Meaning |
|---|---|
| `q` | An e-class, treated as a WTA state. |
| `n` | An e-node, treated as a WTA transition. |
| `children(n)` | Ordered child e-classes of e-node `n`. |
| `weight(n)` | Local semiring weight of e-node `n`. |
| `inside(q)` | Aggregate weight for all derivations rooted at e-class `q`. |
| `⊕` | Semiring addition, used to aggregate alternatives. |
| `⊗` | Semiring multiplication, used to compose a parent with child weights. |
| `0̄` | Semiring zero; Dovetail treats composed `0̄` derivations as refuted. |
| `1̄` | Semiring one; identity for composition. |
| `key(x)` | Exact content key of value `x`. |
| `D(q)` | Set of derivations rooted at e-class `q`. |

The WTA recurrence is:

`inside(q) = ⊕_{n ∈ nodes(q)} weight(n) ⊗ ⊗_{c ∈ children(n)} inside(c)`

The derivation completeness contract is:

`Complete(q) ⇒ emitted(q) = { d ∈ D(q) | weight(d) ≠ 0̄ }`

The bounded cyclic contract is:

`BoundedByCycleCut(q) ⇒ emitted(q) ⊆ { d ∈ D(q) | weight(d) ≠ 0̄ }`

The report completeness contract is:

`ReportComplete(r) ⇔ completeness(r) = Complete`

## Naming Boundaries

| Name | Boundary |
|---|---|
| Dovetail | Rewrite semantics and extraction. |
| Rho backend | Lowering and execution bridge from Dovetail semantics to RhoRuntime. |
| Rho machine | Host process-calculus runtime in F1r3node/Rholang. |
| Ascent | Legacy generated Datalog rewrite backend and oracle path. |
| WPDA | Active parser/recognizer architecture upstream of Dovetail. |

## Safety Terms

`unsafe trait SemanticHash` is unsafe because implementors must uphold a
semantic contract that Rust cannot check:

`write_content(x) = write_content(y) ⇔ x ≈ y`

Here `x ≈ y` means observational equality for the value being serialized. If an
implementation violates this, exact-key deduplication can become unsound.
