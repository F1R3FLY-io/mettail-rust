# Concepts and Glossary

Last updated: 2026-06-14

This document defines the names, acronyms, and symbols used by the
Rho-native MeTTaIL integration documents. A term is introduced here before it
is used formally elsewhere.

## Components

| Term | Definition |
|---|---|
| MeTTaIL | The language-definition and compiler layer. MeTTaIL models source languages with grammar, term constructors, equations, rewrites, folds, guards, and metadata. |
| Dovetail | The substrate-neutral rewrite engine for MeTTaIL semantics. Dovetail represents exact keys, facts, saturation, cyclic inside weights, and ambiguity-preserving extraction. |
| F1r3node | The Rust implementation substrate that contains Rholang, RhoRuntime, RSpace, replay, checkpointing, and cost/funding machinery. |
| Rholang | The process language executed by F1r3node. It is based on the reflective higher-order Rho calculus, with processes, quoted names, sends, receives, joins, `new`, and parallel composition. |
| Rho machine | The runtime model formed by Rholang evaluation plus RSpace communication. In this design, it is the scheduler and execution substrate for lowered rewrite networks. |
| RhoRuntime | The F1r3node runtime entry point used by MeTTaIL bridge tests and generated backends. Generated MeTTaIL artifacts are normalized `rhoapi::Par` values injected directly with an explicit budget; source-text evaluation is retained only for hand-authored regression oracles. |
| RSpace | The tuple-space engine used by Rholang communication. It stores data, waiting continuations, joins, checkpoints, and replay logs. |
| Rho backend | The MeTTaIL bridge that lowers Dovetail rewrite semantics into Rho-native Rholang/RSpace programs. |
| CESK runtime backend | The existing MeTTaIL evaluator backend organized around control, environment, store, and continuation state. The Rho-native path is a candidate replacement for this runtime backend only, not for parsing or oracle infrastructure. |
| WPDA parser/recognizer | The active weighted-pushdown-automaton parser and recognizer path. It remains upstream of runtime backend selection and is not made legacy by the Rho-native design. |
| Ascent reference/oracle path | The generated Ascent/Datalog rewrite path retained for differential testing and reference evidence during Rho rollout. Ascent is legacy for production rewrite execution; this oracle role is the retained verification role, and it is not deleted by a CESK runtime-backend flip. |
| RhoNet | A small intermediate calculus introduced by this design. RhoNet contains only contracts, facts, joins, guards, private names, and observation. It is easier to prove correct than full generated Rholang AST. |

## Language and Rewrite Terms

| Term | Definition |
|---|---|
| GSLT | Generalized syntax/law theory. In this repository, it means a language definition with syntax, equations, rewrites, and operational laws. |
| term | A typed abstract syntax tree node in a modeled language. |
| category | A type-level family of terms, such as `Proc`, `Name`, `Expr`, or `Int`. |
| constructor | A grammar/AST production that builds a term. |
| equation | A symmetric identity, written `t ≡ u`, used to place terms in the same equivalence class. |
| rewrite | A directed semantic step, written `t →ᵣ u`, where `r` is the rule name. |
| congruence | The principle that if a subterm rewrites, the enclosing term may rewrite at the corresponding position. |
| fact | A materialized statement in the rewrite engine, such as “term `t` exists” or “`t` rewrites to `u`.” |
| delta fact | A newly discovered fact used to drive semi-naive iteration. |
| normal form | A result term with no outgoing rewrite in the selected operational semantics. |
| ambiguity | The presence of multiple valid parses, derivations, or normal forms that must remain visible until evidence rejects them. |
| exact key | A byte-level key that is injective with respect to the observational identity being represented. It is not a lossy hash. |
| semantic hash | A hash derived from an exact key. It may be used for indexing, but it must not be the identity proof unless its safety contract establishes injectivity for the domain. |
| predicated type | A type-like communication or rewrite constraint expressed as a guard predicate over matched terms. Predicated types are declared by the language layer, consumed by Dovetail as guarded rules, and lowered by the Rho backend only through covered guards, native guard handlers, or explicit rejections. |
| structural predicate | A predicate whose truth is determined by the shape of a value: constructor head, field layout, binding structure, associative-commutative decomposition, or exact-key pattern membership. |
| behavioral predicate | A predicate whose truth depends on a relation, theory, host operation, or runtime state beyond immediate constructor shape, such as arithmetic comparison, reachability, channel compatibility, relation membership, or bounded quantified search. |
| guard sublanguage | The language-defined syntax and semantics for guard predicates, including connective keywords, built-in predicates, typed predicate signatures, theory registrations, and channel/join declarations. |
| typed predicate | A guard predicate whose parameters carry source-language category or type annotations, such as `gt(x: Int, y: Int)`. Typed predicates drive validation, theory routing, and type-specific lowering; they do not create a backend-local type system. |
| theory routing | The mapping from typed guard predicates to analysis or decision procedures, such as arithmetic, unification, or lattice reasoning. The mapping is derived from generated language inventory rather than keyword heuristics. |
| effective Boolean algebra | A decidable Boolean algebra over a possibly infinite domain. It supplies computable `⊥`, `⊤`, `∧`, `∨`, `¬`, and satisfiability operations so symbolic automata can reason over predicates instead of enumerating concrete values. |
| symbolic finite automaton | A finite automaton whose transitions are labeled by predicates from an effective Boolean algebra rather than by individual alphabet symbols. |
| symbolic finite-state transducer | A symbolic automaton with output. It transforms values or value sequences while preserving symbolic guards; useful operations include composition, pre-image, post-image, and functionality checking. |
| guard obligation | A compile-time coverage item induced by `LanguageDef`, such as a declared predicate, a theory registration, a guarded term slot, a structural guard premise, or a Rho-native channel/join declaration. Rust names this item `RhoGuardObligation`. |
| guard disposition | The audited explanation for one guard obligation. Rust names this item `RhoGuardDisposition`; accepted dispositions are Dovetail-core structural matching, effective Boolean algebra, symbolic finite-state transducer, Rho-native join, native handler, or external contract. |

## Rho and RSpace Terms

| Term | Definition |
|---|---|
| process | A Rholang computation. Common forms are `Nil`, send, receive, `new`, match, contract, and parallel composition. |
| name | A Rholang communication subject. Rho calculus names are structured: a name may be the quote of a process. |
| quote | The operation that turns a process into a name. In Rholang syntax, examples include `@"x"` and `@{P}`. |
| drop | The operation that turns a name back into a process, written `*n` in Rholang. |
| send | A non-blocking output on a channel, written `c!(v)` for a linear send or `c!!(v)` for a persistent send. |
| receive | A continuation waiting for data on a channel, written `for (@x <- c) { P }` for a linear receive. |
| persistent receive | A receive that remains installed after firing, written `for (@x <= c) { P }` or as a `contract`. |
| join | An atomic receive over multiple channels. It fires only when all required messages are available. |
| left-perfect matching | A bipartite join-frontier assignment that covers every required left-side join obligation exactly once while using each right-side message or witness slot at most once. Extra right-side slots may remain unused. |
| peek | A receive that reads without consuming. |
| guard | A boolean predicate checked before a receive commits. A failing guard behaves like no match: no data is consumed. |
| COMM | The communication rule: matching output and input synchronize and run the continuation with the received value substituted. |
| resting space | The RSpace state after evaluation reaches quiescence: stored data plus waiting continuations. |
| replay log | A deterministic record of communication events used to replay nondeterministic schedules consistently. |

## Formal Relations and Symbols

| Symbol | Meaning |
|---|---|
| `t, u, v` | Source-language terms. |
| `r` | A rewrite rule name. |
| `t →ᵣ u` | Term `t` rewrites to term `u` by rule `r`. |
| `t →* u` | Zero or more rewrite steps from `t` to `u`. |
| `t ≡ u` | Terms `t` and `u` are equivalent by equations or structural equivalence. |
| `[t]≡` | The equivalence class of `t` under `≡`. |
| `key(t)` | The exact key for `t` or its equivalence class, depending on context. |
| `Fᵢ` | The set of facts known after iteration `i`. |
| `Δᵢ` | The set of facts discovered at iteration `i`. |
| `derive(F, Δ)` | The new facts derivable by applying rules to existing facts `F` and new facts `Δ`. |
| `ρ` | A RhoNet or Rholang/RSpace configuration. |
| `obs(ρ)` | The canonical observation extracted from a resting Rho configuration. |
| `⟦t⟧` | The lowering or denotation of source object `t`. |
| `≈` | Weak operational equivalence, usually weak barbed equivalence or a proof-specific correspondence relation. |
| `⊥` | Impossible, refuted, or absent value depending on the defined lattice. |
| `⊤` | Unrestricted or top value depending on the defined lattice. |
| `μX. f(X)` | The least fixed point of the monotone function `f`. |

## Acronyms

| Acronym | Expansion | Meaning in this design |
|---|---|---|
| AST | Abstract Syntax Tree | The typed parsed representation of source snippets. |
| CESK | Control, Environment, Store, Kontinuation | The state-machine shape of the existing runtime evaluator backend targeted by the Rho-native replacement path. |
| CBN | Call by Name | A generic lowering strategy in which computations are represented as thunks. |
| CBN/Need | Call by Need | CBN plus memoization of forced thunks. |
| COMM | Communication | The send/receive synchronization rule. |
| DOI | Digital Object Identifier | Persistent identifier for scholarly references. |
| EBA | Effective Boolean Algebra | A decidable Boolean algebra used by symbolic automata and guard theory routing. |
| FV | Formal Verification | Mechanized or mathematically stated correctness evidence. |
| IR | Intermediate Representation | A representation between source terms and emitted runtime code. |
| LTS | Labelled Transition System | A transition system used to state operational correspondence. |
| NF | Normal Form | A term or process with no enabled reduction under a semantics. |
| OSLF | Ordered Linear-Substructural Funding | The funding/cost discipline reused from F1r3node's cost-accounted Rho work. |
| RHO / `ρ` | Reflective Higher-Order | The process-calculus family underlying Rholang. |
| SCC | Strongly Connected Component | A mutually recursive component in a graph. |
| SFA | Symbolic Finite Automaton | A finite automaton over predicates from an effective Boolean algebra. |
| SFT | Symbolic Finite-State Transducer | An output-producing symbolic automaton used for guard-preserving transformations and pre-image reasoning. |
| WFST | Weighted Finite-State Transducer | A finite-state transducer with semiring weights; useful for ranked parsing, extraction, or transformation costs. |
| WTA | Weighted Tree Automaton | A weighted automaton representation used by Dovetail extraction. |

## Naming Convention for Channels

The Rho backend uses structured channel names to avoid collisions:

| Channel family | Purpose |
|---|---|
| `@"mtl:fact:<category>:<key>"` | Stable facts. |
| `@"mtl:delta:<category>:<key>"` | Newly derived facts. |
| `@"mtl:rule:<rule>"` | Rule-control or rule-service channels. |
| `@"mtl:seen:<category>:<key>"` | Deduplication witnesses. |
| `@"mtl#out"` | Sentinel output channel. The `#` separator is intentionally disjoint from the `:` family. |

The sentinel format matters. A free source name such as `out` may ground to a
channel like `@"mtl:out"`, so the observation sentinel uses `@"mtl#out"` to stay
outside that image.
