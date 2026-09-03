# Concepts and Glossary

Last updated: 2026-06-23

Every symbol, acronym, and key term used in this suite is defined here before use
elsewhere. Terms are grouped by layer: the algebra core, the automata/transducers,
the tower, the integration vocabulary, and the runtime/host vocabulary. Each entry
defines a **type, concept, or operation** in prose, then names its canonical anchor
so a reader can jump straight to the ground truth: a Rust type/operation
(`module.rs`) for things that exist as code, and — for results that are *proved* —
the document where the result is **stated and proved as a Definition/Lemma/Theorem**
(doc 12 for the Heyting/behavioral/tier/funding/bisimulation results; doc 02 for the
EBA laws; doc 05 for the closure family; doc 03 for dispatch; doc 04 for
transducers). A Coq theorem name (e.g. `neg_triple`, `excluded_middle_reg`) is given
**only as a parenthetical citation** of the mechanization, never as the substance of
a definition — a reader who has never opened the Coq sources can still understand
every entry.

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
| **Effective Boolean Algebra (EBA)** | An algebra `𝓐 = (Φ, D, ⟦·⟧, ⊤, ⊥, ∧, ∨, ¬, sat, witness)` of predicates over `D` with *computable* Boolean operations, a *decidable* satisfiability test `sat`, and a *witness* generator. "Effective" = every operation is an algorithm, so automata work symbolically without enumerating `D`. Fully developed (with the Boolean laws) in [02 §2](02-effective-boolean-algebra.md#2-the-formal-object); mechanized in `EffectiveBooleanAlgebra.v`. | `trait BooleanAlgebra` (`symbolic.rs`) |
| **Denotation** `⟦φ⟧` | The set of elements satisfying `φ`. `⟦φ ∧ ψ⟧ = ⟦φ⟧ ∩ ⟦ψ⟧`, `⟦¬φ⟧ = D ∖ ⟦φ⟧`. | `BooleanAlgebra::evaluate` |
| **Satisfiability** `sat(φ)` | The decision "is `⟦φ⟧ ≠ ∅`?" — does some element satisfy `φ`. | `BooleanAlgebra::is_satisfiable` |
| **Tautology / validity** | `φ` is valid when `⟦φ⟧ = D`, i.e. `¬φ` is unsatisfiable. | `BooleanAlgebra::is_tautology` |
| **Witness** | A concrete `e ∈ ⟦φ⟧` produced when `φ` is satisfiable — a sample element, useful for counterexamples and term generation. | `BooleanAlgebra::witness` |
| **Overlap** | Two predicates overlap when `⟦φ⟧ ∩ ⟦ψ⟧ ≠ ∅`, i.e. `sat(φ ∧ ψ)`. Guard overlap implies dispatch ambiguity. | `BooleanAlgebra::overlaps` |
| **Minterm** | A maximal satisfiable conjunction of a predicate set and their negations. For guards `{φ₁,…,φₖ}` the minterms partition `D` into classes treated identically by every guard — the finite "effective alphabet" that powers determinization. | `compute_minterms` (`symbolic.rs`) |

## Automata and transducers

| Term | Definition | Canonical anchor |
|---|---|---|
| **Symbolic Finite Automaton (SFA)** | A finite automaton whose transitions are labeled by **predicates** of an EBA rather than concrete symbols. A transition fires when the input element satisfies its guard. SFAs are closed under intersection, union, complement, and determinization, and have decidable emptiness and equivalence. The guard-dispatch soundness/completeness result is stated and proved in [03 §8](03-symbolic-automata-sfa.md#8-the-guard-analysis-use-dispatch-disambiguation) (mechanized in `DispatchCompleteness.v` as `dispatch_completeness`). | `SymbolicAutomaton<A>` (`symbolic.rs`) |
| **Symbolic transition** | An edge `q --[φ]--> q′` that fires on input `e` when `e ⊨ φ`. | `SymbolicTransition<A>` |
| **Symbolic Finite Transducer (SFT)** | An SFA whose transitions additionally carry an **output function** mapping the matched input to output elements: `q --[φ / f]--> q′`. SFTs are closed under composition; single-valuedness (functionality) is decidable. Composition is developed in [04 §5](04-symbolic-transducers-sft-stft.md#5-composition) and functionality in [04 §7](04-symbolic-transducers-sft-stft.md#7-functionality-single-valuedness) (mechanized in `SftComposition.v`, `SftFunctionality.v`). | `SymbolicFiniteTransducer<A,B>` (`sft.rs`) |
| **Output term** | A first-class, *analyzable* output expression `OutputTerm ∈ {Eps, Id, Const, Concat}` carrying a monoid (`Concat`) and a category (`then`), so transducer composition is a precise algebraic operation rather than an opaque closure. Defined in [04 §4](04-symbolic-transducers-sft-stft.md#4-outputterm-a-first-class-analyzable-output-algebra); mechanized in `OutputTermAlgebra.v`. | `OutputTerm<A,B>` (`sft.rs`) |
| **Symbolic Tree Transducer (STFT)** | The tree-structured analog: input is a ranked tree, output is built bottom-up by a relabeling homomorphism. Composition is associative; functionality is preserved. Developed in [04 §8](04-symbolic-transducers-sft-stft.md#8-symbolic-tree-transducers-stft) (mechanized in `StftComposition.v`, `StftFunctionality.v`). | `SymbolicTreeTransducer<A,B>` (`sym_tree_transducer.rs`) |
| **Pre-image / post-image** | For an SFT `T : A → B*`, the pre-image of an SFA over `B` is an SFA over `A` (inputs whose output is accepted); the post-image is the SFA over `B` of all reachable outputs. | `SymbolicFiniteTransducer::pre_image` / `post_image` |
| **Functionality** | An SFT is *functional* (single-valued) when each input maps to at most one output. Composition preserves functionality. | `SymbolicFiniteTransducer::is_functional`; `SftFunctionality.v` |

## Predicate kinds

| Term | Definition | Canonical anchor |
|---|---|---|
| **Structural predicate** | A predicate over the *shape* of data — a constructor pattern, an associative-commutative match, a refinement of a value. Decided **exactly**; its algebra is classical. | `BehavioralPred::AcMatch` (`ast/src/language/model.rs`) |
| **Behavioral predicate** | A predicate over the *dynamics* of a process — reachability, a modal/temporal property (CTL), or a query against an external relation (`halts`, `safe`). Only **semi-decidable**; its complement is unsound to treat classically (the reason its algebra is Heyting, argued in [12 §3](12-heyting-behavioral-logic.md)). | `BehavioralPred::RelationQuery`; `BehavioralAlgebra<H>` (`behavioral_algebra.rs`) |
| **LTS model (`HostTerm`)** | The labeled transition system a behavioral predicate is decided against: a host term type supplying `successors` (one-step edges, backed by the host reduction relation) and `label` (the state's atomic proposition). From a root, the *complete finite reachable LTS* is built by breadth-first search. The Boolean checker does not silently truncate because edge removal is not reject-safe for universal modalities. | `trait HostTerm` (`behavioral_algebra.rs`); defined in [12 §4.1, Definition 4.1](12-heyting-behavioral-logic.md#41-definitions-the-behavioral-algebra) |
| **Behavioral / CTL operators** | The branching-time guard vocabulary `ax / ex / ef / ag / af / eg / au / eu` (e.g. `ag φ` invariance, `ef φ` reachability, `au(φ, ψ)` "φ until ψ"), defined as sugar over the modal fixpoint constructors `⟨a⟩ / [a] / μX / νX`. Evaluation is exact greatest/least-fixpoint model checking over the complete finite reachable LTS. | `ag` / `ef` / `au` / … (`behavioral_algebra.rs`); defined in [12 §4.1, Definition 4.4](12-heyting-behavioral-logic.md#41-definitions-the-behavioral-algebra) |
| **Modal μ-calculus** | The modal/temporal logic with least (`μX.φ`) and greatest (`νX.φ`) fixpoint binders over the modalities `⟨a⟩`/`[a]`; the modal fragment of the behavioral Heyting algebra, subsuming CTL on a finite LTS. Its syntax, fixpoint semantics, model-checking algorithm, and CTL encoding are developed in [15](15-mu-calculus.md). | `Mu`/`Nu`/`FixVar` (`behavioral_algebra.rs`) |
| **Least / greatest fixpoint (`μX.φ` / `νX.φ`)** | The `⊆`-least / `⊆`-greatest solution `T` of `T = ⟦φ⟧[X := T]`: liveness/eventuality (`μ`) versus safety/invariance (`ν`); computed by Kleene iteration from `∅` / the all-states set, converging in `≤ |S|` steps over the finite powerset lattice ([15 §3](15-mu-calculus.md)). | `Mu` / `Nu` (`behavioral_algebra.rs`) |
| **Knaster–Tarski theorem** | Every monotone operator on a complete lattice has a least and a greatest fixpoint — the existence guarantee behind `μ`/`ν`; with finite convergence it is the model-checking algorithm ([15 Theorem 3.4, Lemma 3.7](15-mu-calculus.md)). | [Tarski, 1955](references.md#tarski-1955) |
| **Bisimulation** | The observational equivalence `p ∼ q` (matched steps on both sides) that is the **well-definedness condition** for behavioral predicates: bisimilar processes satisfy the same behavioral guards, so a guard is a property of the process *up to behavior*, not its representation. Decided by partition refinement to the coarsest bisimulation refining an initial coloring. | `struct Lts` / `bisimilar` (`bisimulation.rs`); defined in [12 §5, Theorem 5.4](12-heyting-behavioral-logic.md#5-bisimulation-behavioral-predicates-are-observational); mechanized in `RegisterEquivalence.v` as `is_bisimulation`, `bisimilar` |
| **Quantified predicate** | A predicate `∀x ∈ dom. φ` or `∃x ∈ dom. φ` over a bounded or enumerable domain; modeled three ways (relational enumeration, modal `⋂`/`⋃` denotation, bounded EBA occupancy atom) and treated in full in [14 — Quantification](14-quantification.md). | `BehavioralPred::Quantified`; `prattail/src/logict.rs` |
| **Active domain** | The finite set of all constants appearing in the fact base — the closed-world universe a relational quantifier ranges over, which makes a relational `∀`/`∃` decidable ([14 §2](14-quantification.md)). | `FactBase::active_domain` (`behavioral_algebra.rs`) |
| **`QuantifiedDomain`** | The domain a quantifier ranges over; the substrate carries four shapes (AST `Option<Ident>` + a separate bound, logict `Relation`/`Bounded`, runtime `Named`/`Bounded`/`Enumerated`, modal `QDomain`), bridged by the lowering of [14 §8](14-quantification.md). | `logict.rs`, `behavioral_pred.rs`, `behavioral_algebra.rs` |
| **`Top`** | The always-true predicate stand-in used at compile time when the real predicate is per-instance runtime data — preserves guard-set analysis without committing a value. | `BehavioralPred::Top` |

## The algebra tower

| Term | Definition | Canonical anchor |
|---|---|---|
| **`Sat3`** | Three-valued satisfiability `{Sat, Unsat, DontKnow}` with Kleene `∧`/`∨`/`¬`. A classical algebra never returns `DontKnow`; a semi-decidable one returns it when a bounded search neither found a witness nor proved emptiness. ⚠ `Sat3` is a **Rust** enum (`algebra_tower.rs`), *not* a Coq object. | `enum Sat3` (`algebra_tower.rs`) |
| **`RejectSafeAlgebra`** | The weakest tier: `∧`, `∨`, `pseudo_complement`, and `is_satisfiable_3v → Sat3`. Its only laws are SAT-soundness and double-negation-soundness — **no involutive complement, no excluded middle**. Sound for semi-decidable behavioral algebras. (Reject-safety is [05 Definition 2.1](05-algebra-pyramid-and-decidability.md#2-the-three-tiers); the laws bundle is mechanized in `EffectiveBooleanAlgebra.v` as the record `RejectSafeLaws`.) | `trait RejectSafeAlgebra` (`algebra_tower.rs`) |
| **`HeytingAlgebra`** | `: RejectSafeAlgebra` plus intuitionistic `implies` (`→`, the right adjoint of `∧`) and `regularize` (`¬¬`). Models behavioral predicates where `¬¬a = a` holds only on *regular* elements. The full algebra of `→` and `¬¬` (and why it is the correct home for behavioral guards) is developed in [12 §2](12-heyting-behavioral-logic.md); mechanized in `HeytingAlgebra.v`. | `trait HeytingAlgebra` (`algebra_tower.rs`) |
| **`BooleanAlgebra` (classical tier)** | The classical EBA with an involutive `not` and 2-valued `is_satisfiable` that the SFA complement/determinization/equivalence require. *This* is the trait all automata algorithms are bounded on. | `trait BooleanAlgebra` (`symbolic.rs`) |
| **`Classical<A>`** | A wrapper lifting a classical `BooleanAlgebra` into the reject-safe / Heyting tiers without touching its implementors (`pseudo_complement = not`, `regularize = id`, `is_satisfiable_3v` only ever `Sat`/`Unsat`, `implies = ¬a ∨ b`). | `struct Classical<A>` (`algebra_tower.rs`) |
| **`RejectSafeProduct<S,B>`** | The mixed structural × behavioral guard algebra. It is `RejectSafeAlgebra` **only** (statically never `BooleanAlgebra`), and its `pseudo_complement` is the asymmetric De Morgan `¬(a ∧ b) = (¬a ∧ ⊤) ∨ (⊤ ∧ ¬b)` (`¬a` exact, `¬b` reject-safe) — a reject-safe over-approximation: the padded complement never fires on a satisfiable product (stated and proved as [12 — Heyting Behavioral Logic, Theorem 6.1](12-heyting-behavioral-logic.md); mechanized in `BehavioralNegation.v` as `mixed_negation_soundness`). | `struct RejectSafeProduct<S,B>` (`algebra_tower.rs`) |
| **Reject-safe** | A decision discipline that may **reject** a satisfiable element but **never admits** an unsatisfiable one — conservative/fail-closed: a "no witness found" within budget yields rejection, never a false fire. | `algebra_tower` module doc |
| **Regular element** | In a Heyting algebra, an element fixed by the `¬¬` closure operator (`¬¬a = a`) — the elements where classical reasoning is recovered: `¬` is involutive and the excluded middle holds. The regular elements form a Boolean algebra (the *Booleanization*; see next entry), so they are exactly the decidable/structural fragment of a mixed predicate type. | concept stated and proved in [12 §2.3](12-heyting-behavioral-logic.md#23-the-regular-elements-the-booleanization) (Lemma 2.11, Theorem 2.12); mechanized in `HeytingAlgebra.v` as `neg_involutive_on_regular`, `excluded_middle_reg` |
| **Booleanization / Glivenko** | The construction recovering a classical Boolean algebra from a Heyting algebra: the regular elements, ordered by the **De Morgan join** `a ⊔ b := ¬(¬a ∧ ¬b)`, form a Boolean algebra in which `a ⊔ ¬a = ⊤` for every `a`. The name honours Glivenko's theorem. This is the precise sense in which Heyting *completes* Boolean — Boolean is the all-regular special case, recovered on the regular sublattice. | concept stated and proved in [12 §2.3, Theorem 2.12](12-heyting-behavioral-logic.md#23-the-regular-elements-the-booleanization); mechanized in `HeytingAlgebra.v` as `bjoin`, `excluded_middle_reg` |

## Decidability and quality

| Term | Definition | Canonical anchor |
|---|---|---|
| **`DecidabilityTier`** | `T1 CompileTimeDecidable` / `T2 RuntimeDecidable` / `T3 SemiDecidable` / `T4 Undecidable` — the per-predicate classification by *when* it can be decided. The weakest leg of a combination dominates (`max_tier`); the tier ↔ regularity correspondence (`T1`/`T2 = Reg`, `T3 = Boundary`, `T4 = Closed`) is stated and proved in [12 — Proposition 6.3](12-heyting-behavioral-logic.md). | `enum DecidabilityTier` (`symbolic.rs`); mechanized in `GuardTierCertificate.v` |
| **`GuardTier`** | The macro/Rho mirror of `DecidabilityTier`: `T1Exact / T2Decidable / T3Bounded / T4Asserted`. The tier lattice is a join-semilattice under the combinator `tier_max`; that combination is sound- and complete-flag homomorphic (a product is exactly as classical as its most behavioral leg), and the tiers correspond to the regular core via the *tier ↔ regularity* result (stated and proved as [12 — Heyting Behavioral Logic, Proposition 6.3](12-heyting-behavioral-logic.md); mechanized in `GuardTierCertificate.v` as `tier_max_sound_hom`, `tier_max_complete_hom`). | `RhoGuardTier` (`guard_quality.rs`) |
| **Guard obligation** | A demand induced by a `language!` definition that *some* guard be discharged: a builtin-predicate set, a theory registration, a channel/join, or a per-rule behavioral guard. | `RhoGuardObligationKind` (`rholang-codegen/src/backend.rs`); `collect_guard_obligations` |
| **Disposition** | The *mechanism* chosen to cover an obligation: `DovetailCoreStructural`, `EffectiveBooleanAlgebra`, `SymbolicFiniteTransducer`, `RhoNativeJoin`, `NativeHandler`, or `ExternalContract`. | `RhoGuardDispositionKind` (`backend.rs`) |
| **Quality** | The 7-value evidence grade of a disposition: `ExactDecidable`, `BoundedDecidable`, `RejectSafeApprox`, `TrustedNativeGuard`, `MachineCheckedModel`, `RuntimeObservation`, `Unknown`. Only `Unknown` is fail-closed (refuses the production default). | `RhoGuardQuality` (`guard_quality.rs`) |
| **Coverage evidence** | The fail-closed gate datum: either `NoGuardObligations` or `CoveredGuardObligations`, requiring an *exact* cover (no uncovered, extraneous, or invalid obligation). | `RhoGuardCoverageEvidence` (`backend.rs`); `guard_disposition_covers` |
| **Flip / flip gate** | The decision to make the Rho backend a language's production default. Gated by `Coverage(L) ∧ ArtifactValidation(L) ∧ NoNewDeadlocks(L)`; any `Unknown`-quality obligation blocks it. The fail-closed gate is stated and proved in [07 §5](07-language-to-rholang-integration.md#5-admission-the-fail-closed-flip-gate) (mechanized in `RhoBackendFlipGate.v`). | `decide_rho_flip` (`rholang-codegen/src/flip.rs`) |
| **`HM01` base-sort consistency** | An always-on lint (`hindley_milner.rs`) that re-derives each constructor's principal arrow type from the grammar and flags a base-sort mismatch — a constructor whose inferred result sort differs from its declared category — beneath the staged-analysis refinements. It is base-*sort* inference, not term inference; it fires unconditionally and is inert on the current grammar corpus (0 firings). Mechanized in `HindleyMilnerWiringSound.v` (`hm_principal_arrow_wf`, `hm_consistency_exact`, `hm01_lint_sound`). | `hindley_milner.rs`; [10 §2.6](10-formal-verification-and-tests.md) |

## The constraint-theory engine (LogicT)

| Term | Definition | Canonical anchor |
|---|---|---|
| **LogicT / `LogicStream`** | The backtracking logic monad — a lazily-produced stream of search answers, the engine that evaluates theory and quantified guards. | `LogicStream<T>` (`prattail/src/logict.rs`); [13](13-constraint-theory-engine.md) |
| **`msplit`** | The one primitive of `LogicStream`: produce the next answer and the remaining search, `LogicStream<T> → Option<(T, LogicStream<T>)>`. Every other operation derives from it. | `LogicStream::msplit` |
| **Fair disjunction (`interleave`)** | A round-robin merge of two searches, so a shallow answer in a late branch is never starved by an infinite early branch. The reason a bounded search finds a witness where depth-first diverges. | `LogicStream::interleave` |
| **`fair_conjoin`** | Fair monadic bind (`≫-`): map each answer to a sub-search and `interleave` the results. | `LogicStream::fair_conjoin` |
| **`ConstraintTheory`** | A domain solver — `propagate`, `is_consistent`, `witness`, `evaluate`, and a `label` enumerator. The base contract permits incomplete bounded search and therefore does not imply classical decidability. | `trait ConstraintTheory` (`logict.rs`) |
| **`DecidableConstraintTheory`** | An additional capability whose total `decide_exact` operation proves either a checked witness or exact emptiness for every complete theory predicate. | `trait DecidableConstraintTheory` (`logict.rs`) |
| **`TheoryAlgebra`** | The capability-gated bridge. For every `ConstraintTheory`, it supplies bounded, fair, certificate-checked `RejectSafeAlgebra` reasoning with `Sat3`; only `T: DecidableConstraintTheory` supplies the classical `BooleanAlgebra` consumed by exact automata algorithms. | `TheoryAlgebra<T>` (`logict.rs`); [13 §2](13-constraint-theory-engine.md) |
| **`TriState`** | Three-valued `{ True, False, Unknown }` with Kleene `∧`/`∨`/`¬` and `into_safe_bool` (`Unknown → false`) — the in-crate twin of `Sat3`, produced by the theory-guided quantifier evaluator. | `enum TriState` (`logict.rs`) |
| **`evaluate_quantified`** | The evaluator for a `QuantifiedFormula` (`∀x ∈ dom. φ` / `∃x ∈ dom. φ`); the theory-guided variant returns `TriState`. | `evaluate_quantified` / `evaluate_quantified_with_theory` (`logict.rs`) |

## Funding, GSLT, and the runtime/host vocabulary

| Term | Definition | Canonical anchor |
|---|---|---|
| **GSLT** | *Graph-structured lambda theory* — a language definition viewed as syntax + equations + rewrites + operational laws. Dovetail's saturation **is** its reduction relation. | `docs/design/dovetail-engine/oslf-gslt-native-fold-reduction.md`; `MettaGsltPresentation.v` |
| **The funding discipline** | The cost/resource discipline deciding *which* rewrites may fire, via `is_funded(Δ, Σ, margin) = Δ + margin ≤ Σ`. Its funding judgment is fail-closed and decidable, obeying four laws — sound, reject-underfunded, supply-monotone, decidable — stated and proved in [12 — Proposition 7.1](12-heyting-behavioral-logic.md#7-the-funding-affinity) and [09](09-funding-composition.md). A separate cost-accounting extension of the rho calculus (the cost-accounted rho calculus / cost endofunctor; Meredith, 2026) — **not** OSLF (see the OSLF row below). | `is_funded` (`rholang-adapter/src/gslt.rs`); mechanized in `MettaFundingLawsConformance.v` as `metta_resource_logic_is_funding_sound` |
| **Funding** | The funding-discipline judgment that a rewrite's demand `Δ` is met by the available supply `Σ` with a margin: `Δ + margin ≤ Σ`. Reject-underfunded is the resource-side analog of reject-safe. | `is_funded` (`rholang-adapter/src/gslt.rs`) |
| **OSLF** | *Operational Semantics in Logical Form* — the Stay–Meredith program presenting a calculus's operational semantics as a Gph-enriched multisorted Lawvere theory (sorts = grammar categories, morphisms = constructors, hom-graph edges = one-step rewrites) and deriving its behavioral logic and type structure functorially. **Distinct from the funding discipline above** — the two were formerly conflated in this suite. | [Stay & Meredith, 2017](references.md#stay-meredith-2017) |
| **COMM** | A Rholang communication: a `for`-receive meeting a `!`-send on a shared channel, atomically consuming the message and spawning the continuation. The unit of run-time guard enforcement; a guarded COMM commits *iff* names match and the guard holds (the run-time mirror of [12 — Theorem 6.1](12-heyting-behavioral-logic.md), detailed in [08](08-runtime-comm-enforcement.md)). | mechanized in `RhoGuardedCommSoundness.v` as `comm_fires_iff` |
| **Guard atomicity** | The run-time guarantee that a *failed* guard consumes no facts and emits no output, while a later satisfying datum can still commit (the no-commit-on-false contract of [08](08-runtime-comm-enforcement.md)). | mechanized in `GuardedCommSoundness.v` as `failed_guard_no_commit` |
| **`where`-guard** | A Rholang receive guard `for(@x <- @c where x > 0){…}` that f1r3node evaluates before commit. Enforceable on source-level boolean predicates over bound ground values. | `rho_guard_oracle.rs` |
| **`RhoNativeJoin`** | The disposition (and run-time mechanism) for guards that are **not** `rhoapi::Par`-representable — multi-channel joins and external-relation behavioral guards. A native join handler at the RSpace boundary gates the COMM; generated Rholang does not evaluate the predicate. | `RhoGuardDispositionKind::RhoNativeJoin`; `RhoGuardedCommSoundness.v` |
| **Classify-only boundary** | The architectural fact that the prattail substrate runs **at compile time** and emits *evidence + quality*, never an EBA/SFT structure into generated Rholang. Enforcement at run time is the host's job. | `any-algebra-substrate.md §8`; [08](08-runtime-comm-enforcement.md) |
| **Three concretization mechanisms** | The three ways a behavioral predicate's truth is actually computed: **(i)** μ-calculus model checking over a `HostTerm` LTS, **(ii)** closed-world relational facts in a `FactBase` snapshot, and **(iii)** host observation at COMM time (the production Rholang path — the substrate only *classifies*, f1r3node decides). Selected by the guard's fragment and the backend. | defined in [12 §4.2](12-heyting-behavioral-logic.md#42-the-three-concretization-mechanisms) |

## Acronyms at a glance

| Acronym | Expansion |
|---|---|
| EBA | Effective Boolean Algebra |
| SFA | Symbolic Finite Automaton |
| SFT | Symbolic Finite Transducer |
| STFT | Symbolic Tree Transducer |
| CTL | Computation Tree Logic (the modal/temporal logic of behavioral predicates) |
| NFA / DFA | Nondeterministic / Deterministic Finite Automaton |
| OSLF | Operational Semantics in Logical Form (distinct from the funding discipline) |
| GSLT | Graph-structured lambda theory |
| COMM | Rholang communication reduction |
| AC | Associative-Commutative (matching) |
| RSpace | the F1r3node tuple-space that schedules COMMs |
