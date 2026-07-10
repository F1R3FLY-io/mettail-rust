# References

Last updated: 2026-07-10

This bibliography supports the Rho-native MeTTaIL integration documents. DOI
links are included only where a DOI was verified or is part of a publisher
record. Some foundational books, standards, repository-local documents, and ACL
Anthology records do not provide DOIs.

Local filesystem paths in this bibliography are written relative to the
`mettail-rust` repository root. Paths beginning with `../f1r3node-rust/` refer
to the sibling F1r3node repository in the same workspace.

## Process Calculi, Rho Calculus, and Rholang

### RHO-2005

L. G. Meredith and M. Radestock. 2005. "A Reflective Higher-Order Calculus."
Electronic Notes in Theoretical Computer Science.
[DOI: 10.1016/j.entcs.2005.05.016](https://doi.org/10.1016/j.entcs.2005.05.016).

Used for: the Rho calculus basis of quoted processes as names, reflection,
drop/quote behavior, and COMM-style process reduction.

### LYBECH-2022

Stian Lybech. 2022. "Encodability and Separation for a Reflective Higher-Order
Calculus." arXiv:2209.02356.
[arXiv](https://arxiv.org/abs/2209.02356).

Used for: modern discussion of the Rho calculus, its structured-name behavior,
and the caution that full abstraction and encodability claims need precise
criteria.

### PI-1992-I

Robin Milner, Joachim Parrow, and David Walker. 1992. "A Calculus of Mobile
Processes, I." Information and Computation.
[DOI: 10.1016/0890-5401(92)90008-4](https://doi.org/10.1016/0890-5401%2892%2990008-4).

Used for: background on mobile-process calculi and operational reasoning about
communication.

### PI-1992-II

Robin Milner, Joachim Parrow, and David Walker. 1992. "A Calculus of Mobile
Processes, II." Information and Computation.
[DOI: 10.1016/0890-5401(92)90009-5](https://doi.org/10.1016/0890-5401%2892%2990009-5).

Used for: continuation of the π-calculus foundations.

### JOIN-2000

Cédric Fournet and Georges Gonthier. 2002. "The Join Calculus: A Language for
Distributed Mobile Programming." In *Applied Semantics*. Springer.
[DOI: 10.1007/3-540-45699-6_6](https://doi.org/10.1007/3-540-45699-6_6).

Used for: the intuition that multi-channel synchronization can be treated as a
language-level concurrency primitive.

### RHOLANG-DOCS

F1r3node repository documentation:

- `../f1r3node-rust/docs/rholang/02-syntax-reference.md`
- `../f1r3node-rust/docs/rholang/08-channels-and-concurrency.md`
- `../f1r3node-rust/docs/rholang/crate-overview.md`

Used for: the implementation-facing behavior of Rholang sends, receives,
contracts, joins, guards, parallel composition, and RhoRuntime evaluation.

## Knotted-Topoi Program (North-Star Sources)

### KNOTTED-TOPOI-2026

L. G. Meredith. 2026. "Knotted Topoi: the lift of the knotted set-theoretic
universe, and fully abstract denotational semantics for the category of
graph-structured lambda theories." Manuscript, June 2026.

- `../publications/knotted-topoi/knotted-topoi.tex`

Used for: the declared north-star operational-to-denotational construction. It
fixes the MeTTaIL-to-core-rho desugaring schema, the location channels
`c(ℓ) = ⌜ℓ⌝`, the context-labelled operational correspondence (Proposition and
Obligation "opcorr"), freshness-by-quoting, persistence-by-reflection, equations
as structural congruence, and the channel-intension freedom that licenses
set-automaton-assisted matching. This is the primary source for
[Knotted-Topoi Operational Invariants](13-knotted-topoi-operational-invariants.md).

### KNOTTED-UNIVERSE-2026

L. G. Meredith. 2026. "A Knotted Universe: a new notion of reflective set
theories." Manuscript, 2026.

Used for: the two-sorted reflective set-theory foundation (red and black copies,
each colour's atoms the other's sets), the colour-swap involution, and the
risk-ledger accounting the knotted-topoi paper lifts one categorical level.

### QUOTING-COLOUR-SWAP-2026

L. G. Meredith. 2026. "Quoting is Colour-Swap: a model of the rho calculus in the
knotted universe." Manuscript, 2026.

Used for: the fully abstract rho-calculus denotation, context-bisimulation as a
congruence via idem-pushout (Leifer-Milner) context labels, the behaviour
functor and its final coalgebra, and the reflection idiom for persistent
installation of receivers without replication.

### OPTIMAL-CHANNEL-NAMING-2026

L. G. Meredith. 2026. "Optimal Channel Naming for Compositional Rewrite
Translations via Set Automaton Partial Evaluation." F1R3FLY.io, 2026.

Used for: the optimal (symbol-once, condition O1) set-automaton channel-naming
scheme; the pattern-receive unfolding into nested single-name receives with
name-equality guards (its Section 2.2); and the statement that the optimal
scheme and the verbatim-location scheme induce the same context-labelled
transition system.

### SET-AUTOMATON-MATCHING-2022

M. Bouwman and R. Erkens. 2022. "Term rewriting based on set automaton
matching." arXiv:2202.08687.
[arXiv](https://arxiv.org/abs/2202.08687).

Used for: the set-automaton matching algorithm underlying the optimal
channel-naming scheme, and the host-side match that the corrected
set-automaton-assisted lowering model uses to produce a substitution.

### SET-AUTOMATON-LOCATE-2021

R. Erkens and J. F. Groote. 2021. "A Set Automaton to Locate All Pattern Matches
in a Term." In *Theoretical Aspects of Computing — ICTAC 2021*, Lecture Notes in
Computer Science, vol. 12819, pages 67-85. Springer.
[DOI: 10.1007/978-3-030-85315-0_5](https://doi.org/10.1007/978-3-030-85315-0_5).
[arXiv:2106.15311](https://arxiv.org/abs/2106.15311).

Used for: the set automaton that visits each subject function symbol exactly once
to locate all pattern matches — the O1 "symbol-once" locate discipline the in-Rho
matcher rides to find the beta-redex before seeding the substitution cascade.

## Tuple Spaces, RSpace, and Dataflow

### LINDA-1985

David Gelernter. 1985. "Generative Communication in Linda." ACM Transactions
on Programming Languages and Systems.
[DOI: 10.1145/2363.2433](https://doi.org/10.1145/2363.2433).

Used for: tuple-space communication as a coordination model.

### RSPACE-DOCS

F1r3node repository documentation:

- `../f1r3node-rust/docs/rspace/README.md`
- `../f1r3node-rust/rspace++/src/rspace/reporting_rspace.rs`

Used for: the RSpace API, `produce`, `consume`, joins, checkpoints, replay, and
state inspection.

### KAHN-1974

Gilles Kahn. 1974. "The Semantics of a Simple Language for Parallel
Programming." In *Information Processing 74*. North-Holland.

Used for: the general dataflow intuition that process networks can be described
semantically by the availability and flow of data. No DOI was found for this
conference publication.

## Rewriting, E-Graphs, and Saturation

### KNUTH-BENDIX-1970

Donald E. Knuth and Peter B. Bendix. 1970. "Simple Word Problems in Universal
Algebras." In *Computational Problems in Abstract Algebra*. Pergamon Press.

Used for: the relationship between equations, rewrite systems, confluence, and
normal forms. No DOI was found for this book chapter.

### HUET-1980

Gérard Huet. 1980. "Confluent Reductions: Abstract Properties and Applications
to Term Rewriting Systems." Journal of the ACM.
[DOI: 10.1145/322217.322230](https://doi.org/10.1145/322217.322230).

Used for: rewrite-system confluence background.

### SEKAR-RAMESH-RAMAKRISHNAN-1995

R. C. Sekar, R. Ramesh, and I. V. Ramakrishnan. 1995. "Adaptive Pattern
Matching." SIAM Journal on Computing 24 (6): 1207-1234.
[DOI: 10.1137/S0097539793246252](https://doi.org/10.1137/S0097539793246252).

Used for: the adaptive pattern-matching lineage and the discrimination-net worst
case — a $`\Theta(n^2)`$ blow-up in match states for $`n`$ overlapping patterns —
that the interned-DAG set automaton linearizes to $`2n+1`$ states, the
size-optimality result in
[21 — Set-Automata Optimization Theory](21-set-automata-optimization-theory.md).

### EQUALITY-SATURATION-2009

Ross Tate, Michael Stepp, Zachary Tatlock, and Sorin Lerner. 2009. "Equality
Saturation: A New Approach to Optimization." POPL.
[DOI: 10.1145/1480881.1480915](https://doi.org/10.1145/1480881.1480915).

Used for: e-graph/equality-saturation motivation for retaining many equivalent
program forms before extraction.

### DATALOG-BOOK

Serge Abiteboul, Richard Hull, and Victor Vianu. 1995. *Foundations of
Databases*. Addison-Wesley.
[Online edition](http://webdam.inria.fr/Alice/).

Used for: fixed-point and Datalog-style rule evaluation background. No DOI was
found for the book.

## Lambda Calculus and Explicit Substitutions

### DEBRUIJN-1972

N. G. de Bruijn. 1972. "Lambda Calculus Notation with Nameless Dummies, a Tool
for Automatic Formula Manipulation, with Application to the Church-Rosser
Theorem." Indagationes Mathematicae 34 (5): 381-392.
[DOI: 10.1016/1385-7258(72)90034-0](https://doi.org/10.1016/1385-7258%2872%2990034-0).

Used for: the nameless (de-Bruijn) index representation of bound variables that
makes alpha-equivalence syntactic identity, so capture-avoidance is an arithmetic
condition on indices — the representation the in-Rho binder reflection and the
substitution TRS are built on.

### EXPLICIT-SUBST-1991

M. Abadi, L. Cardelli, P.-L. Curien, and J.-J. Lévy. 1991. "Explicit
Substitutions." Journal of Functional Programming 1 (4): 375-416.
[DOI: 10.1017/S0956796800000186](https://doi.org/10.1017/S0956796800000186).

Used for: the lambda-sigma calculus lineage — substitution and shifting promoted
to first-class rewrite operators — of which the in-Rho de-Bruijn subst/shift TRS
is the sigma-fragment, and the explicit-substitution sharing discipline named as
the cost mitigation.

### CURIEN-HARDIN-LEVY-1996

P.-L. Curien, T. Hardin, and J.-J. Lévy. 1996. "Confluence Properties of Weak and
Strong Calculi of Explicit Substitutions." Journal of the ACM 43 (2): 362-397.
[DOI: 10.1145/226643.226675](https://doi.org/10.1145/226643.226675).

Used for: the confluence and termination theory of the explicit-substitution
sigma-fragment, the theoretical basis for the strong-normalization and
Church-Rosser results proved for the in-Rho substitution TRS.

## Weighted Deduction and Extraction

### HUANG-CHIANG-2005

Liang Huang and David Chiang. 2005. "Better k-best Parsing." Proceedings of
the Ninth International Workshop on Parsing Technology, pages 53-64. ACL.
[ACL Anthology W05-1506](https://aclanthology.org/W05-1506/).

Used for: lazy best-first extraction over hypergraphs, which informs Dovetail's
complete-on-demand best-first derivation enumeration.

### NEWTON-MONOTONE-2010

Javier Esparza, Stefan Kiefer, and Michael Luttenberger. 2010. "Computing the
Least Fixed Point of Positive Polynomial Systems." arXiv:1001.0340.
[arXiv](https://arxiv.org/abs/1001.0340).

Used for: Newton-style least-fixed-point computation background for recursive
weight equations. The Dovetail docs cite this as theoretical context; the
repository's formal boundary still treats the general n-dimensional solver as
an explicit contract.

## Formal Methods

### TLA-2002

Leslie Lamport. 2002. *Specifying Systems: The TLA+ Language and Tools for
Hardware and Software Engineers*. Addison-Wesley.
[Official PDF](https://lamport.azurewebsites.net/tla/book.html).

Used for: finite state and scheduling-harness modeling.

### COQ-ROCQ

Rocq Prover documentation.
[Official site](https://rocq-prover.org/).

Used for: mechanized theorem proving targets in `formal/rocq/` and
`dovetail/formal/rocq/`.

## Repository-Local Formal Artifacts

### DOVETAIL-DESIGN-DOCS

Repository-local Dovetail design documents:

- `docs/design/dovetail-engine/cyclic-closure-design.md`
- `docs/design/dovetail-engine/dovetail-core-implementation-plan.md`
- `docs/design/dovetail-engine/extractor-design.md`
- `docs/design/dovetail-engine/m-rho-0-implementation-plan.md`

Used for: Dovetail's exact-key, saturation, extraction, cyclic-closure, and
M-RHO.0 design lineage.

### RHOLANG-TARGET-DESIGN

Repository-local Rholang target design:

- `docs/design/made/rholang-target/design.md`

Used for: the prior MeTTaIL-to-Rholang target architecture, generic call-by-name
encoding, and Rholang/Rho-machine integration direction.

### RHO-FLIP-DESIGN

Repository-local M-RHO rollout design:

- `docs/design/rho-flip/01-mrho1-execution-contract.md`
- `docs/design/rho-flip/02-red-team-ledger.md`

Used for: M-RHO.1 execution contracts, red-team constraints, rollout staging,
and claim-boundary discipline.

### PREDICATED-TYPES-DESIGN

Repository-local predicated-types design:

- `docs/design/predicated-types.md`

Used for: guarded communication, structural and behavioral predicates,
`guards {}` language inventory, typed predicate overloads, theory routing,
channel/join declarations, and the no-commit semantics for failed guards.

### DOVETAIL-FORMAL

Repository-local Dovetail formal suite:

- `dovetail/formal/rocq/theories/Extraction/NBestExtraction.v`
- `dovetail/formal/rocq/theories/Extraction/EnumerationCompleteness.v`
- `dovetail/formal/rocq/theories/Extraction/LazyFrontierOrder.v`
- `dovetail/formal/rocq/theories/Extraction/OrderPreservingFraming.v`
- `dovetail/formal/rocq/theories/Extraction/CyclicEnumerationImpossibility.v`
- `dovetail/formal/rocq/theories/InsideWeights/InsideWeightSccClosure.v`
- `dovetail/formal/rocq/theories/Saturation/DovetailSaturation.v`
- `dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v`
- `dovetail/formal/rocq/theories/Requirements/LanguageDefInventory.v`
- `dovetail/formal/rocq/theories/Lowering/PatternLoweringSoundness.v`
- `dovetail/formal/rocq/theories/Refinement/RuntimeReportBridge.v`
- `dovetail/formal/rocq/theories/Refinement/RhoReportHandoff.v`

Used for: current Dovetail proof coverage, including the checked runtime report
boundary, the finite-exhaustiveness impossibility result for productive cyclic
enumeration, and the Rho handoff rule that complete reports expose exactly
their root exact keys while bounded cycle-cut reports expose no Rho
observations.

### METTAIL-RUNTIME-FORMAL

Repository-local runtime formal suite:

- `formal/rocq/prattail_wpda_runtime/theories/ExactReachabilityDedup.v`

Used for: exact semantic-key reachability in the MeTTaIL runtime boundary used
by Dovetail extraction and Rho observation oracles.

### RHO-BRIDGE-FORMAL

Repository-local Rho bridge formal suite:

- `formal/rocq/rho_bridge/theories/BridgeInertness.v`
- `formal/rocq/rho_bridge/theories/HostRhoMachineReuse.v`
- `formal/rocq/rho_bridge/theories/MettaGsltPresentation.v`
- `formal/rocq/rho_bridge/theories/MettaOslfLawsConformance.v`
- `formal/rocq/rho_bridge/theories/RhoLoweringTotalOrRejects.v`
- `formal/rocq/rho_bridge/theories/RhoRejectedCoverage.v`
- `formal/rocq/rho_bridge/theories/RhoParWellFormedness.v`
- `formal/rocq/rho_bridge/theories/RhoArtifactBoundary.v`
- `formal/rocq/rho_bridge/theories/CommReductionCorrespondence.v`
- `formal/rocq/rho_bridge/theories/RhoCommScheduleFamily.v`
- `formal/rocq/rho_bridge/theories/LinearCommCorrespondence.v`
- `formal/rocq/rho_bridge/theories/RhoGroundingAndNames.v`
- `formal/rocq/rho_bridge/theories/RhoObservationFingerprint.v`
- `formal/rocq/rho_bridge/theories/AmbiguityWitnessEnumeration.v`
- `formal/rocq/rho_bridge/theories/RhoCallByNeedObservation.v`
- `formal/rocq/rho_bridge/theories/RhoCallByNeedBudget.v`
- `formal/rocq/rho_bridge/theories/DeltaOneMinCostJoin.v`
- `formal/rocq/rho_bridge/theories/DeltaOneMinCostMatching.v`
- `formal/rocq/rho_bridge/theories/GuardedCommSoundness.v`
- `formal/rocq/rho_bridge/theories/AmbiguitySetPreservation.v`
- `formal/rocq/rho_bridge/theories/RhoCostAxisSeparation.v`
- `formal/rocq/rho_bridge/theories/RhoEscrowSettlement.v`
- `formal/rocq/rho_bridge/theories/RhoPurseDeterminism.v`
- `formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v`
- `formal/rocq/rho_bridge/theories/OracleQuotientEquivalence.v`

Used for: current M-RHO proof coverage from one-way bridge shape through
Rho-machine reuse, exact rejected-rule delegation, normalized-`Par` validation,
generated-backend source-text exclusion, COMM correspondence, exact observation,
guard behavior, ambiguity preservation, cost separation, arity-parametric
independent-redex COMM schedules, call-by-need budget admission,
escrow/refund settlement, per-purse determinism, and backend flip gating.

### S-BINDER-FORMAL

Repository-local in-Rho binder beta-substitution artifacts:

- `rholang-codegen/src/rho_net_subst_trs.rs`
- `rholang-runtime/tests/rho_net_beta_firing.rs`
- `rholang-runtime/tests/rho_net_subst_trs_reducer.rs`
- `formal/rocq/rho_bridge/theories/BinderReflectionTotalOrReject.v`
- `formal/rocq/rho_bridge/theories/DeBruijnSubstTRS.v`
- `formal/rocq/rho_bridge/theories/InRhoBetaCascadeWeakBisim.v`
- `formal/rocq/advanced_automata/theories/InRhoMatchPositional.v`

Used for: the in-Rho de-Bruijn substitution/shift TRS (the five reserved
receivers), its zero-admission strong-normalization, confluence, and normal-form
proof, the object-beta weak bisimulation, the reflection totality and injectivity,
the positional match with report-independent reduct separation, and the
live-reducer firing evidence. Primary source for
[In-Rho Binder Beta-Substitution](19-in-rho-binder-beta-substitution.md).

### IN-RHO-CAMPAIGN-FORMAL

Repository-local Epic-4 in-Rho matching campaign formal suite. The end-to-end
verification document [22](22-end-to-end-formal-verification.md) presents these as
numbered QED theorems; the coverage matrix
[23](23-coverage-and-correctness.md) and the completion audit
[24](24-in-rho-completion-audit.md) map each theorem to its runtime evidence.

Matching layer:

- `formal/rocq/advanced_automata/theories/InRhoMatchPositional.v`
- `formal/rocq/advanced_automata/theories/PositionalSetAutomatonSound.v`
- `formal/rocq/advanced_automata/theories/SymbolOnceInjective.v`
- `formal/rocq/advanced_automata/theories/TcChannelNamingQuotient.v`
- `formal/rocq/advanced_automata/theories/PrunePreservesWork.v`
- `formal/rocq/advanced_automata/theories/InRhoReuseDeterminism.v`
- `formal/rocq/advanced_automata/theories/InRhoAcMatchMultiset.v`
- `formal/rocq/advanced_automata/theories/InRhoSameCLTSWeakBisim.v`
- `formal/rocq/advanced_automata/theories/AcAtomicNoPartialConsume.v`
- `formal/rocq/advanced_automata/theories/AcRestReconstruction.v`
- `formal/rocq/advanced_automata/theories/AcMapKeyUniqueness.v`
- `formal/rocq/advanced_automata/theories/AcBagRhsReflection.v`

Firing and capstone layer:

- `formal/rocq/rho_bridge/theories/ContextualAtomicJoinPlugging.v`
- `formal/rocq/rho_bridge/theories/NonLinearEqConsistency.v`
- `formal/rocq/rho_bridge/theories/AtomicFiringNoPartialMatch.v`
- `formal/rocq/rho_bridge/theories/AmbientOpenFiring.v`
- `formal/rocq/rho_bridge/theories/AmbientInOutFiring.v`
- `formal/rocq/rho_bridge/theories/NativeSystemProcessBoundary.v`
- `formal/rocq/rho_bridge/theories/CommRuleFiring.v`
- `formal/rocq/rho_bridge/theories/DeBruijnSubstTRS.v`
- `formal/rocq/rho_bridge/theories/InRhoBetaCascadeWeakBisim.v`
- `formal/rocq/rho_bridge/theories/BinderReflectionTotalOrReject.v`
- `formal/rocq/rho_bridge/theories/EndToEndCommCorrespondence.v`
- `formal/rocq/rho_bridge/theories/WholeGsltInRhoOpCorrespondence.v`
- `formal/rocq/rho_bridge/theories/WholeGsltInRhoOpCorrespondenceOptimalViaSameClts.v`
- `formal/rocq/rho_bridge/theories/WholeGsltInRhoOpCorrespondenceInOutViaFiring.v`

Used for: the machine-checked, zero-admission proof that every non-semantic-
predicate rewrite family matches AND fires in Rho — the per-family per-step COMM
correspondences (base / contextual / AC-linear / AC-structural / binder-β / native
/ ambient In-Out), the O1 symbol-once and $`tc(K)`$ channel-naming optimality, the
AC multiset match, the de-Bruijn substitution TRS strong-normalization / confluence
/ normal-form results, and the whole-⟦G⟧ finite-execution operational-correspondence
capstone threaded over the O1-optimal matching (the `rem:nonopt` discharge). Primary
source for [22 — End-to-End Formal Verification](22-end-to-end-formal-verification.md).

### RHO-PROCESS-FORMAL

Repository-local finite process-calculus projections:

- `formal/process/README.md`
- `formal/process/rho_comm_slice.json`
- `formal/process/rho_comm_slice.py`
- `formal/mcrl2/rho_machine/rho_net_comm.mcrl2`
- `formal/mcrl2/rho_machine/dovetail_fact_steps.mcrl2`
- `formal/mcrl2/rho_machine/rho_guarded_join.mcrl2`
- `formal/mcrl2/rho_machine/dovetail_guarded_join.mcrl2`
- `formal/mcrl2/rho_machine/formulas/no_deadlock.mcf`
- `formal/mcrl2/rho_machine/formulas/rho_internal_schedules_complete.mcf`
- `formal/mcrl2/rho_machine/formulas/dovetail_direct_schedules_complete.mcf`
- `formal/mcrl2/rho_machine/formulas/rho_guard_nonconsuming.mcf`
- `formal/mcrl2/rho_machine/formulas/dovetail_guard_nonconsuming.mcf`
- `formal/maude/rho_machine/rho-net.maude`
- `formal/maude/rho_machine/dovetail-rules.maude`
- `formal/maude/rho_machine/checks/comm-schedule.maude`
- `formal/tla/rho_machine/RhoNetScheduler.tla`
- `formal/tla/rho_machine/Safety.cfg`
- `formal/tla/rho_machine/Liveness.cfg`
- `formal/tla/rho_settlement/RhoPurseSettlement.tla`
- `formal/tla/rho_settlement/Safety.cfg`

Used for: finite executable projections of the RhoNet/Dovetail COMM bridge.
The mCRL2, Maude, and TLA+ models are generated from the same JSON slice
specification and checked for drift before model checking. These checks
complement `RhoCommScheduleFamily.v` by model-checking and rewrite-checking a
bounded four-redex process fragment and the matching scheduler boundary. The
Maude projection records visible fire/complete traces while leaving Rho reserve
steps internal, checks all 24 full schedules on both projections, and rejects
every visible completion trace with fewer than all four fires.
The settlement TLA+ model separately checks bounded per-purse reserve
commutation and fail-closed duplicate/missing-purse rejection.

### COVERAGE-MATRIX

Repository-local formal coverage matrix:

- `prattail/docs/theory/formal-verification/coverage-matrix.md`

Used for: current status of Dovetail and M-RHO obligations.
