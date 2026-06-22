# Concepts and Glossary

Last updated: 2026-06-22

Every symbol, acronym, and key term used in this suite is defined here before use
elsewhere. Terms are grouped by layer: the algebra core, the automata/transducers,
the tower, the integration vocabulary, and the runtime/host vocabulary. Each entry
names the canonical Rust type or Coq theorem so a reader can jump straight to the
ground truth.

## How to read the notation

Mathematical expressions are written in unicode and quoted in backticks, e.g.
`⟦φ⟧ ⊆ D`, `a ∧ ¬a = ⊥`, `Σ ≥ Δ + margin`. A predicate is written `φ`, `ψ`; a
domain element `e ∈ D`; an automaton state `q`; a substitution `σ`. The symbol `⊨`
is "satisfies" (`e ⊨ φ` means `e ∈ ⟦φ⟧`); `⊤` is the always-true predicate and `⊥`
the always-false predicate; `≈` is observational/semantic equality.

## Core algebra terms

| Term | Definition | Canonical anchor |
|---|---|---|
| **Predicate** `φ` | A finite description of a (possibly infinite) set of domain elements. Its meaning is its denotation `⟦φ⟧ ⊆ D`. | `BooleanAlgebra::Predicate` (`prattail/src/symbolic.rs`) |
| **Domain** `D` | The set of elements a predicate ranges over (e.g. `ℤ`, `char`, a process term). May be infinite. | `BooleanAlgebra::Domain` |
| **Effective Boolean Algebra (EBA)** | An algebra `𝓐 = (Φ, D, ⟦·⟧, ⊤, ⊥, ∧, ∨, ¬, sat, witness)` of predicates over `D` with *computable* Boolean operations, a *decidable* satisfiability test `sat`, and a *witness* generator. "Effective" = every operation is an algorithm, so automata work symbolically without enumerating `D`. | `trait BooleanAlgebra`; `EffectiveBooleanAlgebra.v` |
| **Denotation** `⟦φ⟧` | The set of elements satisfying `φ`. `⟦φ ∧ ψ⟧ = ⟦φ⟧ ∩ ⟦ψ⟧`, `⟦¬φ⟧ = D ∖ ⟦φ⟧`. | `BooleanAlgebra::evaluate` |
| **Satisfiability** `sat(φ)` | The decision "is `⟦φ⟧ ≠ ∅`?" — does some element satisfy `φ`. | `BooleanAlgebra::is_satisfiable` |
| **Tautology / validity** | `φ` is valid when `⟦φ⟧ = D`, i.e. `¬φ` is unsatisfiable. | `BooleanAlgebra::is_tautology` |
| **Witness** | A concrete `e ∈ ⟦φ⟧` produced when `φ` is satisfiable — a sample element, useful for counterexamples and term generation. | `BooleanAlgebra::witness` |
| **Overlap** | Two predicates overlap when `⟦φ⟧ ∩ ⟦ψ⟧ ≠ ∅`, i.e. `sat(φ ∧ ψ)`. Guard overlap implies dispatch ambiguity. | `BooleanAlgebra::overlaps` |
| **Minterm** | A maximal satisfiable conjunction of a predicate set and their negations. For guards `{φ₁,…,φₖ}` the minterms partition `D` into classes treated identically by every guard — the finite "effective alphabet" that powers determinization. | `compute_minterms` (`symbolic.rs`) |

## Automata and transducers

| Term | Definition | Canonical anchor |
|---|---|---|
| **Symbolic Finite Automaton (SFA)** | A finite automaton whose transitions are labeled by **predicates** of an EBA rather than concrete symbols. A transition fires when the input element satisfies its guard. SFAs are closed under intersection, union, complement, and determinization, and have decidable emptiness and equivalence. | `SymbolicAutomaton<A>` (`symbolic.rs`); `DispatchCompleteness.v` |
| **Symbolic transition** | An edge `q --[φ]--> q′` that fires on input `e` when `e ⊨ φ`. | `SymbolicTransition<A>` |
| **Symbolic Finite Transducer (SFT)** | An SFA whose transitions additionally carry an **output function** mapping the matched input to output elements: `q --[φ / f]--> q′`. SFTs are closed under composition; single-valuedness (functionality) is decidable. | `SymbolicFiniteTransducer<A,B>` (`sft.rs`); `SftComposition.v`, `SftFunctionality.v` |
| **Output term** | A first-class, *analyzable* output expression `OutputTerm ∈ {Eps, Id, Const, Concat}` carrying a monoid (`Concat`) and a category (`then`), so transducer composition is a precise algebraic operation rather than an opaque closure. | `OutputTerm<A,B>` (`sft.rs`); `OutputTermAlgebra.v` |
| **Symbolic Tree Transducer (STFT)** | The tree-structured analog: input is a ranked tree, output is built bottom-up by a relabeling homomorphism. Composition is associative; functionality is preserved. | `SymbolicTreeTransducer<A,B>` (`sym_tree_transducer.rs`); `StftComposition.v`, `StftFunctionality.v` |
| **Pre-image / post-image** | For an SFT `T : A → B*`, the pre-image of an SFA over `B` is an SFA over `A` (inputs whose output is accepted); the post-image is the SFA over `B` of all reachable outputs. | `SymbolicFiniteTransducer::pre_image` / `post_image` |
| **Functionality** | An SFT is *functional* (single-valued) when each input maps to at most one output. Composition preserves functionality. | `SymbolicFiniteTransducer::is_functional`; `SftFunctionality.v` |

## Predicate kinds

| Term | Definition | Canonical anchor |
|---|---|---|
| **Structural predicate** | A predicate over the *shape* of data — a constructor pattern, an associative-commutative match, a refinement of a value. Decided **exactly**; its algebra is classical. | `BehavioralPred::AcMatch` (`ast/src/language/model.rs`) |
| **Behavioral predicate** | A predicate over the *dynamics* of a process — reachability, a modal/temporal property (CTL), or a query against an external relation (`halts`, `safe`). Only **semi-decidable**; its complement is unsound to treat classically. | `BehavioralPred::RelationQuery`; `BehavioralAlgebra<H>` (`behavioral_algebra.rs`) |
| **Quantified predicate** | A predicate `∀x ∈ dom. φ` or `∃x ∈ dom. φ` over a bounded or enumerable domain. | `BehavioralPred::Quantified`; `prattail/src/logict.rs` |
| **`Top`** | The always-true predicate stand-in used at compile time when the real predicate is per-instance runtime data — preserves guard-set analysis without committing a value. | `BehavioralPred::Top` |

## The algebra tower

| Term | Definition | Canonical anchor |
|---|---|---|
| **`Sat3`** | Three-valued satisfiability `{Sat, Unsat, DontKnow}` with Kleene `∧`/`∨`/`¬`. A classical algebra never returns `DontKnow`; a semi-decidable one returns it when a bounded search neither found a witness nor proved emptiness. ⚠ `Sat3` is a **Rust** enum (`algebra_tower.rs`), *not* a Coq object. | `enum Sat3` (`algebra_tower.rs`) |
| **`RejectSafeAlgebra`** | The weakest tier: `∧`, `∨`, `pseudo_complement`, and `is_satisfiable_3v → Sat3`. Its only laws are SAT-soundness and double-negation-soundness — **no involutive complement, no excluded middle**. Sound for semi-decidable behavioral algebras. | `trait RejectSafeAlgebra`; `EffectiveBooleanAlgebra.v` (`RejectSafeLaws`) |
| **`HeytingAlgebra`** | `: RejectSafeAlgebra` plus intuitionistic `implies` (`→`, the right adjoint of `∧`) and `regularize` (`¬¬`). Models behavioral predicates where `¬¬a = a` holds only on *regular* elements. | `trait HeytingAlgebra`; `HeytingAlgebra.v` |
| **`BooleanAlgebra` (classical tier)** | The classical EBA with an involutive `not` and 2-valued `is_satisfiable` that the SFA complement/determinization/equivalence require. *This* is the trait all automata algorithms are bounded on. | `trait BooleanAlgebra` (`symbolic.rs`) |
| **`Classical<A>`** | A wrapper lifting a classical `BooleanAlgebra` into the reject-safe / Heyting tiers without touching its implementors (`pseudo_complement = not`, `regularize = id`, `is_satisfiable_3v` only ever `Sat`/`Unsat`, `implies = ¬a ∨ b`). | `struct Classical<A>` (`algebra_tower.rs`) |
| **`RejectSafeProduct<S,B>`** | The mixed structural × behavioral guard algebra. It is `RejectSafeAlgebra` **only** (statically never `BooleanAlgebra`), and its `pseudo_complement` is the asymmetric De Morgan `¬(a ∧ b) = (¬a ∧ ⊤) ∨ (⊤ ∧ ¬b)` (`¬a` exact, `¬b` reject-safe) — a proven reject-safe over-approximation. | `struct RejectSafeProduct<S,B>`; `BehavioralNegation.v` (`mixed_negation_soundness`) |
| **Reject-safe** | A decision discipline that may **reject** a satisfiable element but **never admits** an unsatisfiable one — conservative/fail-closed: a "no witness found" within budget yields rejection, never a false fire. | `algebra_tower` module doc |
| **Regular element** | In a Heyting algebra, an element with `¬¬a = a`. Classical reasoning is sound on regulars; `excluded_middle` holds there. | `HeytingAlgebra.v` (`neg_involutive_on_regular`, `excluded_middle_reg`) |

## Decidability and quality

| Term | Definition | Canonical anchor |
|---|---|---|
| **`DecidabilityTier`** | `T1 CompileTimeDecidable` / `T2 RuntimeDecidable` / `T3 SemiDecidable` / `T4 Undecidable` — the per-predicate classification by *when* it can be decided. The weakest leg of a combination dominates (`max_tier`). | `enum DecidabilityTier` (`symbolic.rs`); `GuardTierCertificate.v` |
| **`GuardTier`** | The macro/Rho mirror of `DecidabilityTier`: `T1Exact / T2Decidable / T3Bounded / T4Asserted`. The tier lattice is a join-semilattice, proven a homomorphism under combination. | `RhoGuardTier` (`guard_quality.rs`); `GuardTierCertificate.v` (`tier_max_*`) |
| **Guard obligation** | A demand induced by a `language!` definition that *some* guard be discharged: a builtin-predicate set, a theory registration, a channel/join, or a per-rule behavioral guard. | `RhoGuardObligationKind` (`rholang-codegen/src/backend.rs`); `collect_guard_obligations` |
| **Disposition** | The *mechanism* chosen to cover an obligation: `DovetailCoreStructural`, `EffectiveBooleanAlgebra`, `SymbolicFiniteTransducer`, `RhoNativeJoin`, `NativeHandler`, or `ExternalContract`. | `RhoGuardDispositionKind` (`backend.rs`) |
| **Quality** | The 7-value evidence grade of a disposition: `ExactDecidable`, `BoundedDecidable`, `RejectSafeApprox`, `TrustedNativeGuard`, `MachineCheckedModel`, `RuntimeObservation`, `Unknown`. Only `Unknown` is fail-closed (refuses the production default). | `RhoGuardQuality` (`guard_quality.rs`) |
| **Coverage evidence** | The fail-closed gate datum: either `NoGuardObligations` or `CoveredGuardObligations`, requiring an *exact* cover (no uncovered, extraneous, or invalid obligation). | `RhoGuardCoverageEvidence` (`backend.rs`); `guard_disposition_covers` |
| **Flip / flip gate** | The decision to make the Rho backend a language's production default. Gated by `Coverage(L) ∧ ArtifactValidation(L) ∧ NoNewDeadlocks(L)`; any `Unknown`-quality obligation blocks it. | `decide_rho_flip` (`rholang-codegen/src/flip.rs`); `RhoBackendFlipGate.v` |

## The constraint-theory engine (LogicT)

| Term | Definition | Canonical anchor |
|---|---|---|
| **LogicT / `LogicStream`** | The backtracking logic monad — a lazily-produced stream of search answers, the engine that evaluates theory and quantified guards. | `LogicStream<T>` (`prattail/src/logict.rs`); [13](13-constraint-theory-engine.md) |
| **`msplit`** | The one primitive of `LogicStream`: produce the next answer and the remaining search, `LogicStream<T> → Option<(T, LogicStream<T>)>`. Every other operation derives from it. | `LogicStream::msplit` |
| **Fair disjunction (`interleave`)** | A round-robin merge of two searches, so a shallow answer in a late branch is never starved by an infinite early branch. The reason a bounded search finds a witness where depth-first diverges. | `LogicStream::interleave` |
| **`fair_conjoin`** | Fair monadic bind (`≫-`): map each answer to a sub-search and `interleave` the results. | `LogicStream::fair_conjoin` |
| **`ConstraintTheory`** | A domain solver — `propagate`, `is_consistent`, `witness`, `evaluate`, and a `label` enumerator — that becomes a `BooleanAlgebra` for free via `TheoryAlgebra`. | `trait ConstraintTheory` (`logict.rs`) |
| **`TheoryAlgebra`** | The bridge wrapping a `ConstraintTheory` plus a `search_bound` as an effective Boolean algebra (`Predicate = TheoryPred`, `is_satisfiable = witness().is_some()`), so the automata reuse it. | `TheoryAlgebra<T>` (`logict.rs`); [13 §2](13-constraint-theory-engine.md) |
| **`TriState`** | Three-valued `{ True, False, Unknown }` with Kleene `∧`/`∨`/`¬` and `into_safe_bool` (`Unknown → false`) — the in-crate twin of `Sat3`, produced by the theory-guided quantifier evaluator. | `enum TriState` (`logict.rs`) |
| **`evaluate_quantified`** | The evaluator for a `QuantifiedFormula` (`∀x ∈ dom. φ` / `∃x ∈ dom. φ`); the theory-guided variant returns `TriState`. | `evaluate_quantified` / `evaluate_quantified_with_theory` (`logict.rs`) |

## OSLF, GSLT, and the runtime/host vocabulary

| Term | Definition | Canonical anchor |
|---|---|---|
| **GSLT** | *Generalized Syntax/Law Theory* — a language definition viewed as syntax + equations + rewrites + operational laws. Dovetail's saturation **is** its reduction relation. | `docs/design/dovetail-engine/oslf-gslt-native-fold-reduction.md`; `MettaGsltPresentation.v` |
| **OSLF** | *Ordered Linear-Substructural Funding* — the cost/resource discipline deciding *which* rewrites may fire, via `is_funded(Δ, Σ, margin) = Δ + margin ≤ Σ`. Four laws: sound, reject-underfunded, supply-monotone, decidable. The logic-from-a-distributive-law of [Stay & Meredith, 2016](references.md#stay-meredith-2016). | `MettaOslfLawsConformance.v` (`metta_resource_logic_is_oslf_sound`) |
| **Funding** | The OSLF judgment that a rewrite's demand `Δ` is met by the available supply `Σ` with a margin: `Δ + margin ≤ Σ`. Reject-underfunded is the resource-side analog of reject-safe. | `is_funded` (`rholang-adapter/src/gslt.rs`) |
| **COMM** | A Rholang communication: a `for`-receive meeting a `!`-send on a shared channel, atomically consuming the message and spawning the continuation. The unit of run-time guard enforcement. | `RhoGuardedCommSoundness.v` (`comm_fires_iff`) |
| **Guard atomicity** | The run-time guarantee that a *failed* guard consumes no facts and emits no output, while a later satisfying datum can still commit. | `GuardedCommSoundness.v` (`failed_guard_no_commit`) |
| **`where`-guard** | A Rholang receive guard `for(@x <- @c where x > 0){…}` that f1r3node evaluates before commit. Enforceable on source-level boolean predicates over bound ground values. | `rho_guard_oracle.rs` |
| **`RhoNativeJoin`** | The disposition (and run-time mechanism) for guards that are **not** `rhoapi::Par`-representable — multi-channel joins and external-relation behavioral guards. A native join handler at the RSpace boundary gates the COMM; generated Rholang does not evaluate the predicate. | `RhoGuardDispositionKind::RhoNativeJoin`; `RhoGuardedCommSoundness.v` |
| **Classify-only boundary** | The architectural fact that the prattail substrate runs **at compile time** and emits *evidence + quality*, never an EBA/SFT structure into generated Rholang. Enforcement at run time is the host's job. | `any-algebra-substrate.md §8`; [08](08-runtime-comm-enforcement.md) |

## Acronyms at a glance

| Acronym | Expansion |
|---|---|
| EBA | Effective Boolean Algebra |
| SFA | Symbolic Finite Automaton |
| SFT | Symbolic Finite Transducer |
| STFT | Symbolic Tree Transducer |
| CTL | Computation Tree Logic (the modal/temporal logic of behavioral predicates) |
| NFA / DFA | Nondeterministic / Deterministic Finite Automaton |
| OSLF | Ordered Linear-Substructural Funding |
| GSLT | Generalized Syntax/Law Theory |
| COMM | Rholang communication reduction |
| AC | Associative-Commutative (matching) |
| RSpace | the F1r3node tuple-space that schedules COMMs |
