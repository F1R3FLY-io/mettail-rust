# References

This bibliography is intentionally source-of-truth oriented. It favors local
files that are versioned with the implementation and formal artifacts.

## Local Design Documents

- `docs/design/dovetail-engine/dovetail-core-implementation-plan.md`
- `docs/design/dovetail-engine/extractor-design.md`
- `docs/design/dovetail-engine/cyclic-closure-design.md`
- `docs/design/dovetail-engine/semiring-extraction-plan.md`
- `docs/design/dovetail-engine/m-rho-0-implementation-plan.md`
- `docs/architecture/rho-native-integration/README.md`
- `prattail/docs/theory/formal-verification/coverage-matrix.md`

## Rust Source

- `dovetail/src/lib.rs`
- `dovetail/src/key.rs`
- `dovetail/src/egraph.rs`
- `dovetail/src/rules.rs`
- `dovetail/src/wta.rs`
- `dovetail/src/scc.rs`
- `dovetail/src/extract.rs`
- `dovetail/src/report.rs`
- `dovetail/src/space.rs`

## Rust Tests

- `dovetail/tests/bounded_exhaustive.rs`
- `dovetail/tests/properties.rs`
- `dovetail/tests/example_regressions.rs`
- `dovetail/tests/corpus_replay.rs`
- `dovetail/tests/language_inventory.rs`
- `dovetail/tests/language_shape_parity.rs`

## Formal Artifacts

- `dovetail/formal/rocq/theories/ExactKeys/ExactKeyDedup.v`
- `dovetail/formal/rocq/theories/Extraction/NBestExtraction.v`
- `dovetail/formal/rocq/theories/Extraction/EnumerationCompleteness.v`
- `dovetail/formal/rocq/theories/Extraction/LazyFrontierOrder.v`
- `dovetail/formal/rocq/theories/Extraction/OrderPreservingFraming.v`
- `dovetail/formal/rocq/theories/Extraction/ExtractionOutcome.v`
- `dovetail/formal/rocq/theories/Extraction/CycleCutBoundary.v`
- `dovetail/formal/rocq/theories/Extraction/CyclicEnumerationImpossibility.v`
- `dovetail/formal/rocq/theories/InsideWeights/InsideWeightSccClosure.v`
- `dovetail/formal/rocq/theories/Saturation/DovetailSaturation.v`
- `dovetail/formal/rocq/theories/Requirements/LanguageDefInventory.v`
- `dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v`
- `dovetail/formal/rocq/theories/Lowering/PatternLoweringSoundness.v`
- `dovetail/formal/rocq/theories/Refinement/RustModelBridge.v`
- `dovetail/formal/rocq/theories/Refinement/RuntimeReportBridge.v`
- `dovetail/formal/rocq/theories/Refinement/RhoReportHandoff.v`
- `dovetail/formal/rocq/theories/Rigail/NewtonSccAdequacy.v`
- `dovetail/formal/why3/key_budget_contract.mlw`
- `dovetail/formal/creusot/README.md`

## Theory References Used By The Implementation

### EGG-2021

Willsey et al., "egg: Fast and Extensible Equality Saturation", POPL 2021, DOI:
[10.1145/3434304](https://doi.org/10.1145/3434304). Dovetail uses this as the
equality-saturation and e-graph lineage, while replacing finite hash identity
with exact content keys.

### HUANG-CHIANG-2005

Huang and Chiang, "Better k-best Parsing", IWPT 2005, ACL Anthology:
[W05-1506](https://aclanthology.org/W05-1506/). The ACL record has no DOI
field. Dovetail uses this as the lazy-product enumeration lineage; local use:
`docs/design/dovetail-engine/extractor-design.md`.

### ESPARZA-KIEFER-LUTTENBERGER-2008

Esparza, Kiefer, and Luttenberger, "Convergence Thresholds of Newton's Method
for Monotone Polynomial Equations", arXiv:
[0802.2856](https://arxiv.org/abs/0802.2856). Dovetail uses this as background
for Newton-style fixed-point iteration; local bridge:
`dovetail/formal/rocq/theories/Rigail/NewtonSccAdequacy.v`.

### ESPARZA-KIEFER-LUTTENBERGER-2010

Esparza, Kiefer, and Luttenberger, "Computing the Least Fixed Point of Positive
Polynomial Systems", arXiv: [1001.0340](https://arxiv.org/abs/1001.0340).
Dovetail uses this as background for least fixed points of positive systems;
local implementation use: `rigail::solve_scc_weights_newton`.
