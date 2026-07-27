# References

This bibliography is intentionally source-of-truth oriented. It favors local
files that are versioned with the implementation and formal artifacts.

## Local Design Documents

- `docs/design/dovetail-engine/dovetail-core-implementation-plan.md`
- `docs/design/dovetail-engine/extractor-design.md`
- `docs/design/dovetail-engine/cyclic-closure-design.md`
- `docs/design/dovetail-engine/semiring-extraction-plan.md`
- `docs/design/dovetail-engine/m-rho-0-implementation-plan.md`
- `docs/design/dovetail-engine/oslf-gslt-native-fold-reduction.md`
- `docs/architecture/dovetail/10-runtime-facing-reports.md`
- `docs/architecture/rho-native-integration/README.md`
- `prattail/docs/theory/formal-verification/coverage-matrix.md`
- `docs/design/made/ascent_generation.md` (retired Ascent clause shapes quoted in [13](13-egraph-vs-datalog-rewrites.md))
- `docs/design/exploring/performance.md` (the measured class-explosion numbers in [13](13-egraph-vs-datalog-rewrites.md))
- `docs/archive/phase-6/CONGRUENCE-DRIVEN-PROJECTIONS.md` (Datalog AC projection relations cited in [13](13-egraph-vs-datalog-rewrites.md))
- `docs/archive/phase-3/SESSION-EQUATIONAL-REWRITE.md` (the 60–80 s rewrite timings cited in [13](13-egraph-vs-datalog-rewrites.md))
- `docs/design/made/repl.md` (the old REPL `rw_proc` step view contrasted in [13](13-egraph-vs-datalog-rewrites.md))

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
- `macros/src/gen/runtime/binder_congruence.rs` (Ambient binder NativeHandler codegen)
- `macros/src/gen/runtime/dovetail_report.rs` (generated report compiler + handler install)
- `macros/src/gen/runtime/dovetail_report/typed_report.rs` (the step-only `dovetail_step_report` producer cited in [13 §6](13-egraph-vs-datalog-rewrites.md#6-what-each-engine-can-and-cannot-answer))
- `runtime/src/language.rs` (`Language::run_step_backend_report`, the step-report routing point)
- `rholang-runtime/src/backend.rs` (the Dovetail+Rho wrapper that runs the step compiler)

## Rust Tests

- `dovetail/tests/bounded_exhaustive.rs`
- `dovetail/tests/properties.rs`
- `dovetail/tests/example_regressions.rs`
- `dovetail/tests/corpus_replay.rs`
- `dovetail/tests/language_inventory.rs`
- `dovetail/tests/language_shape_parity.rs`
- `dovetail/tests/ac_ambiguity.rs`, `dovetail/tests/ac_lowering_shape.rs` (in-engine AC matching)
- `languages/tests/ambient_binder_handler.rs` (binder float capture-safety)
- `languages/tests/ambient_dovetail_flip.rs` (the Ambient flip: Complete reports)
- `languages/tests/fix_a_alpha_canonical_semantic_key.rs` (FIX-A α-canonical keys)
- `languages/tests/rholang_dovetail_host_routed.rs` (gate excludes host-routed rholang)
- `languages/tests/rholang_dovetail_fold.rs` (native-fold reduction: the worked-examples matrix — `int(1+2,8)→3`, var-defer, bad-cast→`Err`, host-guard)
- `languages/tests/rholang_dovetail_op_enum.rs` (typed op-enum exact-key `SemanticHash` distinctness + `Display`)
- `runtime/tests/canonical_to_bytes.rs` (canonical numeric `to_canonical_bytes` — deterministic, `Eq`-agreeing content-key bytes)

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
- `dovetail/formal/rocq/theories/Saturation/DovetailSaturation.v` (saturation soundness + native-fold soundness `native_fold_saturation_sound` / `native_refire_is_noop` + funding laws `fold_transition_funded` → `funded_fold_saturates_within_budget`)
- `dovetail/formal/rocq/theories/Requirements/LanguageDefInventory.v`
- `dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v`
- `dovetail/formal/rocq/theories/Lowering/PatternLoweringSoundness.v`
- `dovetail/formal/rocq/theories/Lowering/GeneratedReportCompiler.v` (rule-disposition partition incl. the `NativeFoldLowered` native-fold disposition: `native_fold_lowered_requires_structural_support`, `native_fold_requirements_are_exact_key`)
- `dovetail/formal/rocq/theories/Lowering/AmbientBinderHandler.v` (binder capture-safety)
- `dovetail/formal/rocq/theories/Lowering/CollectionAcLowering.v` (AC canonicalization soundness)
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

### CARDELLI-GORDON-2000

Cardelli and Gordon, "Mobile Ambients", Theoretical Computer Science 240(1),
2000, DOI:
[10.1016/S0304-3975(99)00231-5](https://doi.org/10.1016/S0304-3975(99)00231-5).
The source calculus whose binder/freshness structural congruence the
[Binder-Congruence Handler](11-binder-congruence-handler.md) discharges.

### DEBRUIJN-1972

de Bruijn, "Lambda calculus notation with nameless dummies, a tool for automatic
formula manipulation, with application to the Church-Rosser theorem", Indagationes
Mathematicae 34, 1972, DOI:
[10.1016/1385-7258(72)90034-0](https://doi.org/10.1016/1385-7258(72)90034-0).
The nameless-binder encoding behind FIX-A's α-canonical key (α-equivalent bodies
become byte-identical); local use:
[Data Model and Exact Keys](03-data-model-and-exact-keys.md#the-α-canonical-binder-key-fix-a).

### PITTS-2003

Pitts, "Nominal Logic, a First Order Theory of Names and Binding", Information and
Computation 186(2), 2003, DOI:
[10.1016/S0890-5401(03)00138-X](https://doi.org/10.1016/S0890-5401(03)00138-X).
The freshness relation `x # t` and capture-avoidance reasoning the binder handler
and `AmbientBinderHandler.v` use.

### TATE-EQSAT-2009

Tate, Stepp, Tatlock, and Lerner, "Equality Saturation: a New Approach to
Optimization", POPL 2009, pp. 264–276, DOI:
[10.1145/1480881.1480915](https://doi.org/10.1145/1480881.1480915) (resolves via
doi.org to the ACM Digital Library). The equality-saturation-as-reduction lineage
behind treating Dovetail's saturation as the GSLT reduction relation `→*`; local
use:
[Funding/GSLT Native Fold Reduction](../../design/dovetail-engine/oslf-gslt-native-fold-reduction.md).

### NELSON-OPPEN-1980

Nelson and Oppen, "Fast Decision Procedures Based on Congruence Closure", Journal
of the ACM 27(2):356–364, 1980, DOI:
[10.1145/322186.322198](https://doi.org/10.1145/322186.322198) (resolves via
doi.org to the ACM Digital Library). The congruence-closure basis for Dovetail's
rebuild step (`equal children ⇒ equal same-operator parents`); local use:
[Funding/GSLT Native Fold Reduction](../../design/dovetail-engine/oslf-gslt-native-fold-reduction.md).

### GIRARD-1987

Girard, "Linear Logic", Theoretical Computer Science 50(1):1–101, 1987, DOI:
[10.1016/0304-3975(87)90045-4](https://doi.org/10.1016/0304-3975(87)90045-4)
(resolves via doi.org → Elsevier PII `0304397587900454`, which self-encodes the
DOI). The substructural-logic source for the funding discipline's no-contraction reading ("weight
orders, never prunes"); local use:
[Funding/GSLT Native Fold Reduction](../../design/dovetail-engine/oslf-gslt-native-fold-reduction.md).

### BAADER-NIPKOW-1998

Baader and Nipkow, "Term Rewriting and All That", Cambridge University Press,
1998, ISBN 978-0-521-77920-3 (no DOI — a monograph). The term-rewriting reference
for the redex / normal-form / termination vocabulary the fold fragment uses; local
use:
[Funding/GSLT Native Fold Reduction](../../design/dovetail-engine/oslf-gslt-native-fold-reduction.md).

### MOHRI-2002

Mohri, "Semiring Frameworks and Algorithms for Shortest-Distance Problems",
Journal of Automata, Languages and Combinatorics 7(3):321–350, 2002. No registered
(resolvable) DOI; the ACM Digital Library internal id `10.5555/639508.639512` uses
ACM's non-resolvable internal prefix, **not** a real DOI. The semiring / tropical
(min-plus) shortest-distance basis for `rigail`'s inside-weight algebra; local use:
[Funding/GSLT Native Fold Reduction](../../design/dovetail-engine/oslf-gslt-native-fold-reduction.md).

### ASCENT-2022

Sahebolamri, Gilray, and Micinski, "Seamless Deductive Inference via Macros",
Proceedings of the 31st ACM SIGPLAN International Conference on Compiler
Construction (CC 2022), pp. 77–88, DOI:
[10.1145/3497776.3517779](https://doi.org/10.1145/3497776.3517779) (resolves via
doi.org to the ACM Digital Library); evaluation artifact archived at Zenodo, DOI:
[10.5281/zenodo.6330172](https://doi.org/10.5281/zenodo.6330172). Ascent is the
Rust-embedded Datalog engine the retired MeTTaIL rewrite backend generated;
local use: [13 - E-Graph Rewrites vs Datalog Rewrites](13-egraph-vs-datalog-rewrites.md).

### EGGLOG-2023

Zhang, Wang, Flatt, Cao, Zucker, Rosenthal, Tatlock, and Willsey, "Better
Together: Unifying Datalog and Equality Saturation", Proceedings of the ACM on
Programming Languages 7(PLDI), Article 125, 2023, DOI:
[10.1145/3591239](https://doi.org/10.1145/3591239) (resolves via doi.org to the
ACM Digital Library). Shows that Datalog and equality saturation unify in one
framework (egglog); the basis for [13](13-egraph-vs-datalog-rewrites.md)'s point
that the two paradigms are complementary rather than opposed; local use:
[13 - E-Graph Rewrites vs Datalog Rewrites](13-egraph-vs-datalog-rewrites.md).
