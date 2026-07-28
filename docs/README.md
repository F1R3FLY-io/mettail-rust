# MeTTaIL Documentation

Organized documentation for the MeTTaIL project.

---

## Core Documents (Living)

These documents are actively maintained and should always reflect the current state:

- **`main_goals.md`** - Project vision, objectives, and roadmap
- **`getting_started.md`** - Quick start guide for new users
- **`architecture.md`** - System design and implementation overview
- **`architecture/runtime-backend-spine.md`** - Cohesive artifact spine for the Dovetail and Rho runtime-backend replacement path
- **`architecture/dovetail/README.md`** - Standalone Dovetail rewrite engine architecture, design, proof, and handoff suite
- **`architecture/rho-native-integration/README.md`** - Rho-native MeTTaIL / Dovetail / F1r3node integration architecture
- **`architecture/semantic-predicates/README.md`** - Semantic-predicate symbolic algebra (EBA / SFA / SFT / Heyting tower) and its end-to-end `language!`-to-Rholang integration
- **`languages/README.md`** - Per-language references: every bundled `language!` specification explained component by component
- **`contributing.md`** - How to contribute to the project

---

## Dovetail Rewrite Engine Architecture

Pedagogical standalone design suite for Dovetail itself, independent of the Rho
machine backend:

- **`architecture/dovetail/README.md`** - Overview, reading paths, diagrams, and validation
- **`architecture/dovetail/00-executive-brief.md`** - One-page decision brief for principals
- **`architecture/dovetail/00-requirements-traceability.md`** - Explicit Dovetail requirement-to-document coverage map
- **`architecture/dovetail/01-concepts-and-glossary.md`** - Symbols, acronyms, and key terms
- **`architecture/dovetail/02-engine-architecture.md`** - Layers, lifecycle, and component rationale
- **`architecture/dovetail/03-data-model-and-exact-keys.md`** - E-graph model, content keys, framing, and reports
- **`architecture/dovetail/04-rules-and-saturation.md`** - Rules-as-data, matching, instantiation, and budgeted saturation
- **`architecture/dovetail/05-extraction-and-weights.md`** - Best-first derivation extraction and semiring ordering
- **`architecture/dovetail/06-cyclic-closure-and-boundedness.md`** - SCC inside weights, cycle cuts, and completeness reporting
- **`architecture/dovetail/07-formal-verification-and-tests.md`** - Mechanized proof and test coverage matrix
- **`architecture/dovetail/08-engineering-handoff.md`** - Maintenance guide for future agents and implementers
- **`architecture/dovetail/09-worked-example.md`** - End-to-end example from rewrite rules to checked extraction
- **`architecture/dovetail/10-runtime-facing-reports.md`** - What Dovetail reports are, why a rewrite engine needs them, and how consumers must handle them
- **`architecture/dovetail/11-binder-congruence-handler.md`** - How Dovetail evaluates Ambient's binders capture-safely in-engine (float-then-AC-reduce)
- **`architecture/dovetail/12-native-fold-reduction.md`** - How Dovetail reduces a language's `fold` rules (native-computed RHS) in-engine via the typed-`L` op-enum

---

## Rho-Native Execution Architecture

Pedagogical design suite for the MeTTaIL, Dovetail, Rholang, RSpace, F1r3node,
and Rho machine integration:

- **`architecture/rho-native-integration/README.md`** - Executive overview and reading paths
- **`architecture/rho-native-integration/00-executive-brief.md`** - One-page decision brief for principals
- **`architecture/rho-native-integration/00-requirements-traceability.md`** - Explicit requirement-to-document coverage map
- **`architecture/rho-native-integration/01-concepts-and-glossary.md`** - Symbols, acronyms, and key terms
- **`architecture/rho-native-integration/02-end-to-end-architecture.md`** - Source snippet to RhoRuntime lifecycle
- **`architecture/rho-native-integration/03-dovetail-rewrite-semantics.md`** - Dovetail facts, rewrite rules, saturation, extraction, and coverage
- **`architecture/rho-native-integration/04-rho-native-dataflow-lowering.md`** - Compiling rewrite semantics into RhoNet, normalized Rholang AST, and RSpace dataflow
- **`architecture/rho-native-integration/05-rspace-parallel-scheduling.md`** - How RSpace schedules enabled rewrites in parallel
- **`architecture/rho-native-integration/06-correctness-and-coverage.md`** - Mathematical prose proofs and non-claims
- **`architecture/rho-native-integration/07-verification-and-rollout.md`** - M-RHO verification and rollout gates
- **`architecture/rho-native-integration/08-production-runtime-backend-completion.md`** - Production completion gates for replacing the CESK runtime backend path
- **`architecture/rho-native-integration/09-term-level-reduction-split.md`** - Dovetail folds and Rholang COMM composed in one term
- **`architecture/rho-native-integration/10-adaptive-evaluation-model.md`** - Sequential-by-default evaluation, trampoline escalation, and the Tier-3 held-fold contract
- **`architecture/rho-native-integration/11-reactive-comm-stepper.md`** - Lock-free single-stepping of COMM reductions on the Rho machine
- **`architecture/rho-native-integration/12-runtime-invocation-migration.md`** - Migration to the `RhoMachineInvocation` / `RhoBackendInvocation` split
- **`architecture/rho-native-integration/13-knotted-topoi-operational-invariants.md`** - Operational invariants required by the knotted-topoi north-star paper
- **`architecture/rho-native-integration/14-completion-audit.md`** - Campaign completion audit with the per-epic requirement-to-evidence matrix
- **`architecture/rho-native-integration/15-in-rho-set-automaton-matching.md`** - Compiling the set automaton into Rho for O1-optimal in-Rho matching
- **`architecture/rho-native-integration/16-in-rho-verification-plan.md`** - End-to-end formal-verification strategy for the in-Rho matching
- **`architecture/rho-native-integration/17-stage-3-production-wiring.md`** - Wiring the derived in-Rho matching ruleset as a language's default backend
- **`architecture/rho-native-integration/18-in-rho-ac-matching.md`** - Order-independent associative-commutative matching on the interpreter
- **`architecture/rho-native-integration/19-in-rho-binder-beta-substitution.md`** - The in-Rho de-Bruijn substitution TRS cascade for binder beta
- **`architecture/rho-native-integration/20-rholang-runtime-backend.md`** - How the whole in-Rho backend runs on F1r3node's RhoRuntime and RSpace
- **`architecture/rho-native-integration/21-set-automata-optimization-theory.md`** - Why the in-Rho matching is optimal: O1/O2/O3 and the channel naming
- **`architecture/rho-native-integration/22-end-to-end-formal-verification.md`** - The mechanized operational-correspondence theorem suite
- **`architecture/rho-native-integration/23-coverage-and-correctness.md`** - The family-by-capability coverage matrix and empirical probes
- **`architecture/rho-native-integration/24-in-rho-completion-audit.md`** - The in-Rho requirement-to-evidence closing audit
- **`architecture/rho-native-integration/25-in-rho-base-family-reference.md`** - Reconstruction-grade reference for the base-rewrite family
- **`architecture/rho-native-integration/26-in-rho-ac-family-reference.md`** - Reconstruction-grade reference for the associative-commutative family
- **`architecture/rho-native-integration/27-oslf-language-to-rholang-compilation.md`** - Compiling OSLF `language!` specifications to Rholang via the set-automaton pipeline
- **`architecture/rho-native-integration/28-translation-rule-system.md`** - The specification-level translation calculus: the thirteen-rule master table, whole-language assembly, and worked whole-language instances with a test-pinned installed-program listing
- **`architecture/rho-native-integration/29-knotted-topoi-satisfaction-crosswalk.md`** - Per-item crosswalk of the knotted-topoi paper's labeled claims to their mechanized, runtime-tested, or denotational-program status
- **`architecture/rho-native-integration/references.md`** - Citations, DOI links, and repository-local proof references
- **`architecture/rho-native-integration/validate.sh`** - Reproducible local validation for the suite

The cohesive runtime-backend reading path is:

1. **`architecture/runtime-backend-spine.md`** - the compact artifact spine and ownership boundaries
2. **`architecture/dovetail/README.md`** - Dovetail's standalone contract and the direct Dovetail runtime lane
3. **`architecture/dovetail/10-runtime-facing-reports.md`** - the report artifact that connects Dovetail to downstream consumers
4. **`architecture/rho-native-integration/README.md`** - the full artifact spine from `language!` to `RuntimeBackendReport`
5. **`architecture/rho-native-integration/02-end-to-end-architecture.md`** - the stage-by-stage runtime backend replacement path
6. **`architecture/rho-native-integration/04-rho-native-dataflow-lowering.md`** - the AST-first Rho-native lowering details

---

## Semantic-Predicate Symbolic Algebra Architecture

Pedagogical design suite for the *theory-of-guards* layer: effective Boolean
algebras, symbolic finite automata and transducers, the Heyting algebra tower for
behavioral constraints, and the end-to-end path from a `language!` guard through to
Rholang enforcement:

- **`architecture/semantic-predicates/README.md`** - Overview, reading paths, diagramming policy, and validation
- **`architecture/semantic-predicates/00-executive-brief.md`** - One-page decision brief for principals
- **`architecture/semantic-predicates/00-requirements-traceability.md`** - Requirement-to-document coverage map
- **`architecture/semantic-predicates/01-concepts-and-glossary.md`** - Symbols, acronyms, and key terms
- **`architecture/semantic-predicates/02-effective-boolean-algebra.md`** - The EBA, decision procedures, minterms, and instances
- **`architecture/semantic-predicates/03-symbolic-automata-sfa.md`** - Predicate-labeled automata: recognition, closure, determinization
- **`architecture/semantic-predicates/04-symbolic-transducers-sft-stft.md`** - Symbolic (tree) transducers, output-term algebra, composition, functionality
- **`architecture/semantic-predicates/05-algebra-pyramid-and-decidability.md`** - The reject-safe / Heyting / Boolean tower, `Sat3`, tiers, and the closure family
- **`architecture/semantic-predicates/06-guard-syntax-and-extensions.md`** - Supported guard syntax and proposed extensions for the unsupported features
- **`architecture/semantic-predicates/07-language-to-rholang-integration.md`** - Guard declaration to classified obligation, disposition, quality, and the fail-closed flip gate
- **`architecture/semantic-predicates/08-runtime-comm-enforcement.md`** - How the surviving guard is enforced at run time (and what Rholang does not do)
- **`architecture/semantic-predicates/09-funding-composition.md`** - How the predicate algebra composes with the funding discipline at the guarded-COMM boundary
- **`architecture/semantic-predicates/10-formal-verification-and-tests.md`** - The mechanized-proof matrix and the zero-admission gate
- **`architecture/semantic-predicates/11-worked-example.md`** - GuardedRho end-to-end to a host-routed join
- **`architecture/semantic-predicates/12-heyting-behavioral-logic.md`** - Why Heyting/intuitionistic logic governs behavioral constraints, bisimulation invariance, and the funding affinity
- **`architecture/semantic-predicates/references.md`** - Citations, DOI links, and repository-local proof references
- **`architecture/semantic-predicates/validate.sh`** - Reproducible local validation for the suite

---

## Language Specification References

One page per bundled `language!` specification in `languages/src/`, walking the block
component by component: what every DSL fragment means, what the macro generates from
it, and how the result executes — each claim traced to a file and line in the parser,
the generator, or the generated output:

- **`languages/README.md`** - Suite index: the roster of bundled languages, where to start, page conventions, and the diagramming policy
- **`languages/lambda.md`** - `Lambda` (the λ-calculus): binders and higher-order abstract syntax, β-reduction via the `eval` meta-operator, and congruence rules as reduction contexts — the recommended first read for the DSL
- **`languages/validate.sh`** - Reproducible local validation for the suite

Pages for `Monoid`, `Json`, `Turing`, `Pi`, `Ambient`, `Calculator`, and `Rholang` are
tracked in the suite roster and not yet written.

---

## Guides (Topical)

Focused guides on specific features:

- **`guides/theory_syntax.md`** - Complete `theory!` macro syntax reference
- **`guides/collections.md`** - Collection types and pattern matching
- **`guides/bindings.md`** - Variable binding and substitution
- **`guides/repl.md`** - Interactive REPL usage (→ `REPL-GUIDE.md`)
- **`guides/wfst_features.md`** - WFST features: weighted dispatch, beam pruning, training

---

## Language Specification Composition

Comprehensive treatment of every form of language composition (five
mechanisms, theory/correctness, future operators, morphisms):

- **`composition/README.md`** - Entry point + four reading paths
- **`composition/00_overview.md`** - Taxonomy + decision flowchart + pipeline
- **`composition/glossary.md`** - Master glossary of terms & symbols
- **`composition/bibliography.md`** - Numbered references with DOIs

Browse the subdirectories for in-depth coverage of foundations, mechanisms,
formal semantics, correctness, system interactions, morphisms, additional
operators, diagnostics, examples, implementation, and comparison.

---

## Design Documents

Detailed technical designs:

### Made (Implemented)
- **`design/made/ascent_generation.md`** - How Datalog rules are generated
- **`design/made/data_structures.md`** - Collections and binding design
- **`design/made/repl.md`** - Term explorer REPL design
- **`design/made/wfst_integration.md`** - WFST integration: feature gates, dispatch strategy, benchmarks

### Exploring (In Progress / Future)
- **`design/exploring/theory_composition.md`** - Module system design
- **`design/exploring/k_framework_comparison.md`** - Comparison with K Framework
- **`design/exploring/performance.md`** - Performance analysis and optimization

---

## Historical (Archive)

Development history organized by phase:

- **`archive/phase-1/`** - Initial implementation (parsing, binding, substitution)
- **`archive/phase-2/`** - Parser generation and rewrite engine
- **`archive/phase-3/`** - Collections and optimization
- **`archive/phase-6/`** - Equations and congruence rules

**Note**: Archive is for historical reference. Check core docs for current state.

---

## Internal (Meta)

Internal documentation about the documentation itself:

- **`meta/ide_linting.md`** - Handling IDE false positives
- **`meta/phase_naming.md`** - Development phase organization

---

## Reading Path for New Contributors

1. **Start**: `getting_started.md` - Learn basics
2. **Understand**: `architecture.md` - See how it works
3. **Explore**: `guides/` - Deep dive into specific features
4. **Design**: `design/made/` - Understand implementation decisions
5. **Contribute**: `contributing.md` - Make changes

---

## Reading Path for Researchers

1. **Vision**: `main_goals.md` - Understand objectives
2. **Theory**: `guides/theory_syntax.md` - See formal language
3. **Design**: `design/made/ascent_generation.md` - Execution model
4. **Performance**: `design/exploring/performance.md` - Optimization strategies
4.5. **WFSTs**: `guides/wfst_features.md` → `../../prattail/docs/{theory,architecture,design,usage}/wfst/` - Weighted parsing
5. **Future**: `main_goals.md` → Theory Translation section

---

## Maintenance

### When to Update Core Docs
- ✅ Major feature completion
- ✅ API changes
- ✅ Architecture changes
- ✅ New milestones reached

### When to Create New Docs
- ✅ New major feature needs explanation
- ✅ Complex design needs documentation
- ✅ Common questions need answers
- ❌ Don't create for every minor change

### When to Archive
- ✅ Phase/milestone complete
- ✅ Design decisions finalized
- ✅ Information superseded by new approach
- ❌ Don't delete - move to `archive/`

---

## Documentation Style

- **Lowercase filenames**: `main_goals.md`, not `MAIN-GOALS.md`
- **Underscores for spaces**: `theory_syntax.md`, not `theory-syntax.md`
- **Clear structure**: Use headings, lists, code blocks
- **Examples**: Show, don't just tell
- **Concise**: Respect reader's time
- **Current**: Update "Last Updated" date

---

**Last Updated**: July 2026
