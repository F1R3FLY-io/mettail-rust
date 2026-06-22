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
- **`architecture/symbolic-predicates/README.md`** - Semantic-predicate symbolic algebra (EBA / SFA / SFT / Heyting tower) and its end-to-end `language!`-to-Rholang integration
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

- **`architecture/symbolic-predicates/README.md`** - Overview, reading paths, diagramming policy, and validation
- **`architecture/symbolic-predicates/00-executive-brief.md`** - One-page decision brief for principals
- **`architecture/symbolic-predicates/00-requirements-traceability.md`** - Requirement-to-document coverage map
- **`architecture/symbolic-predicates/01-concepts-and-glossary.md`** - Symbols, acronyms, and key terms
- **`architecture/symbolic-predicates/02-effective-boolean-algebra.md`** - The EBA, decision procedures, minterms, and instances
- **`architecture/symbolic-predicates/03-symbolic-automata-sfa.md`** - Predicate-labeled automata: recognition, closure, determinization
- **`architecture/symbolic-predicates/04-symbolic-transducers-sft-stft.md`** - Symbolic (tree) transducers, output-term algebra, composition, functionality
- **`architecture/symbolic-predicates/05-algebra-pyramid-and-decidability.md`** - The reject-safe / Heyting / Boolean tower, `Sat3`, tiers, and the closure family
- **`architecture/symbolic-predicates/06-guard-syntax-and-extensions.md`** - Supported guard syntax and proposed extensions for the unsupported features
- **`architecture/symbolic-predicates/07-language-to-rholang-integration.md`** - Guard declaration to classified obligation, disposition, quality, and the fail-closed flip gate
- **`architecture/symbolic-predicates/08-runtime-comm-enforcement.md`** - How the surviving guard is enforced at run time (and what Rholang does not do)
- **`architecture/symbolic-predicates/09-oslf-composition.md`** - How the predicate algebra composes with OSLF funding at the guarded-COMM boundary
- **`architecture/symbolic-predicates/10-formal-verification-and-tests.md`** - The mechanized-proof matrix and the zero-admission gate
- **`architecture/symbolic-predicates/11-worked-example.md`** - GuardedRho end-to-end to a host-routed join
- **`architecture/symbolic-predicates/12-heyting-behavioral-logic.md`** - Why Heyting/intuitionistic logic governs behavioral constraints, bisimulation invariance, and the OSLF affinity
- **`architecture/symbolic-predicates/references.md`** - Citations, DOI links, and repository-local proof references
- **`architecture/symbolic-predicates/validate.sh`** - Reproducible local validation for the suite

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

**Last Updated**: June 2026
