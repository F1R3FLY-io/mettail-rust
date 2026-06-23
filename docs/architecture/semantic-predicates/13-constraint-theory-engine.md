# The Constraint-Theory Engine: LogicT Under the Substrate

Last updated: 2026-06-23

All symbols are defined in [Concepts and Glossary](01-concepts-and-glossary.md).
The algebra documents ([02](02-effective-boolean-algebra.md)–[05](05-algebra-pyramid-and-decidability.md))
treat predicates abstractly; this document is the **engine underneath** them —
**LogicT**, the backtracking logic-monad and constraint-theory framework
(`prattail/src/logict.rs`) that actually *evaluates* quantified predicates,
*combines* theories, and *adapts* a domain solver into an effective Boolean algebra
the automata reuse. It is the integration narrative; the full API and algorithm
reference is `prattail/docs/design/constraint-theories/logict-framework.md`, to
which this page links for depth.

## 1. What LogicT is, and why fair backtracking

LogicT is the Rust realization of the Haskell-lineage **backtracking logic monad**
([Kiselyov, Shan, Friedman & Sabry, 2005](references.md#kiselyov-2005)). A search
for satisfying assignments is a *stream of answers* produced lazily; the engine is
`LogicStream<T>`, a backtracking stream whose one primitive is

`msplit : LogicStream<T> → Option<(T, LogicStream<T>)>`

— "produce the next answer and the rest of the search," from which every other
operation derives. The operations that matter for guard evaluation are the **fair**
ones:

| Operation | Role |
|---|---|
| `mplus` | unfair disjunction (depth-first concatenation) |
| `interleave` | **fair** disjunction — round-robin merge, so a late answer is never starved by an infinite early branch |
| `fair_conjoin` | **fair** bind (`≫-`) — map each answer to a sub-search and interleave the results |
| `once` / `ifte` | hard cut and soft cut (committed choice) |
| `gnot` | negation as finite failure (closed-world) |
| `collect_bounded(limit)` | the bounded-search harness — at most `limit` `msplit` steps |

![Fair interleaving versus unfair depth-first search](figures/13-logict-backtracking.svg)

PlantUML source: [figures/13-logict-backtracking.puml](figures/13-logict-backtracking.puml).

Fairness is the whole point for a guard engine. A behavioral or theory guard induces
a search tree that may have an infinite early branch and a shallow witness in a late
branch. Unfair `mplus` descends the infinite branch forever and never reaches the
witness — it would report `Sat3::DontKnow` where an answer exists. Fair `interleave`
round-robins the branches, so a bounded budget (`collect_bounded`) is spent
breadth-first and the shallow witness is found. **This is precisely why the bounded
search can return `Sat` where naive depth-first would diverge into `DontKnow`** —
and the reason the engine uses an explicit `VecDeque` of branches rather than
continuation-passing.

## 2. The bridge: `ConstraintTheory` → `TheoryAlgebra` → effective Boolean algebra

The substrate's automata are written *once* against the `BooleanAlgebra` trait
([02 §3](02-effective-boolean-algebra.md)). LogicT supplies the adapter that lets a
domain-specific solver plug into that interface without touching the automata.

![A registered constraint theory becomes a Boolean algebra the automata reuse](figures/13-theory-algebra-bridge.svg)

PlantUML source: [figures/13-theory-algebra-bridge.puml](figures/13-theory-algebra-bridge.puml).

A **`ConstraintTheory`** (the trait in `logict.rs`) is a domain solver: a `Store`, a
`propagate(store, constraint) → Option<Store>` step, an `is_consistent` check, a
`witness(store) → Option<Assignment>`, an `evaluate(constraint, assignment) → bool`,
and a `label(store) → LogicStream<Constraint>` enumerator. A *decidable* theory
returns `LogicStream::empty()` from `label` (propagation alone decides); a theory
that needs search returns a fair stream.

**`TheoryAlgebra<T: ConstraintTheory>`** wraps a theory plus a `search_bound` and
`impl`s `BooleanAlgebra` with `Predicate = TheoryPred<T>` (a `True | False | Atom |
And | Or | Not` tree) and `Domain = T::Assignment`. Its `is_satisfiable` is
`witness(...).is_some()`, where `witness` runs `collect_constraints` — `And` via
`fair_conjoin`, `Or` via `interleave`, `Not` by De Morgan push-down to negation-as-
failure — then `collect_bounded(search_bound)`, then `theory.witness` (falling back
to `label` + `propagate`), validating each candidate with `evaluate`. The payoff
sentence:

> **Once a domain implements `ConstraintTheory`, it is a `BooleanAlgebra` for free —
> hence a `SymbolicAutomaton`, minterms, determinization, and the overlap/subsumption
> analysis of [03](03-symbolic-automata-sfa.md) and [07](07-language-to-rholang-integration.md)
> apply unchanged.** This is how a `theories { name = T for [Cat] }` registration
> ([06 §2.1.3](06-guard-syntax-and-extensions.md)) becomes a usable guard algebra.

This lift holds for every domain whose satisfiability is **decidable**. One
shipped backend is deliberately held *back* from it, because its satisfiability
is only **semi-decidable** — the Z3/SMT oracle of §2.1.

The three shipped theories — `PresburgerTheory`, `UnificationTheory`,
`LatticeTheory` — return an empty `label` (decidable: propagation only, the
`search_bound` is irrelevant), except `UnificationTheory`'s extended custom-match,
whose non-empty `label` engages the fair search bounded by `search_bound` (the
`LT01` lint guards it). `PresburgerAlgebra` additionally has a *direct*
`BooleanAlgebra` path (NFA-backed, [02 §5](02-effective-boolean-algebra.md)) for
speed, distinct from the bridge.

### 2.1 The Z3/SMT backend — a `ConstraintTheory` that deliberately stops there

The payoff above has **one deliberate exception**. `Z3Theory`
(`prattail/src/logict_smt.rs`, feature `smt`, default-off — it dynamically links
the system `libz3`) is a `ConstraintTheory` over `bool`, linear integer
arithmetic, and fixed-width bit-vectors, but it is **never** lifted to a
`TheoryAlgebra<Z3Theory>` and **never** becomes a `BooleanAlgebra`. The reason is
soundness, not convenience.

A general SMT query has three outcomes — `Sat`, `Unsat`, and `unknown` — and
`unknown` is irreducibly semi-decidable. The generic bridge of §2 decides
satisfiability by `witness(...).is_some()`, a **two-valued** test; routing Z3
through it would collapse `unknown → witness None → is_satisfiable false`,
silently reporting a wrong **`Unsat`** (the exact defect in the upstream
lling-llang hoist this backport corrects). So the backend is exposed **only**
through a three-valued surface — `logict_smt::is_satisfiable_3v` and
`checked_witness`, returning `Sat3 = Sat | Unsat | DontKnow`
([05 §3](05-algebra-pyramid-and-decidability.md)) — and a Z3 `unknown` maps to
`DontKnow`, **never** to `Unsat`. `DontKnow` then meets the same reject-safe
collapse the rest of the engine uses (`Unknown → false`, §5). In the bridge
figure above, this is the amber Z3 leg that branches off `ConstraintTheory` to a
`Sat3` exit and stops — it never reaches the `BooleanAlgebra` node.

Two further disciplines keep it sound:

- **Verified deciders stay primary.** Z3 is a **secondary gap-filler**, consulted
  only where a verified decider — the Presburger NFA
  ([02 §5](02-effective-boolean-algebra.md)), the interval, or the ordered-field
  algebra — itself returns `DontKnow` on a mixed numeric/bit-vector guard the
  hand-rolled leaves cannot express. It is **never** routed into the classical SFA
  consumers (complement, determinization, equivalence) that require a *total*
  Boolean algebra.
- **Every witness is certificate-checked.** A reported `Sat` model is
  re-`evaluate`d before it is believed, so the oracle can never fabricate a
  satisfying assignment (`Z3WitnessChecked.v` — `checked_witness_sound`,
  `checked_witness_no_fabrication`, mechanized zero-admission,
  [10 §2.1](10-formal-verification-and-tests.md)).

The first consumer is **refinement-subtyping entailment**:
`RefinementTypeSystem::predicate_entails`
(`prattail/src/type_system/refinement.rs`) decides `premise ⟹ conclusion` over
mixed numeric/bit-vector refinements by asking Z3 whether `premise ∧ ¬conclusion`
is unsatisfiable — `Unsat ⇒ entailment holds`, `Sat ⇒ it does not`, and
`DontKnow ⇒ do not claim entailment` (the reject-safe default; the non-`smt`
build computes the same judgement without Z3). `GuardTierCertificate` classifies a
Z3-decided guard at tier `T3`, degrading to `T4` on an `unknown`
([05 §6](05-algebra-pyramid-and-decidability.md)).

## 3. Quantified-predicate evaluation

A `∀x ∈ dom. φ` or `∃x ∈ dom. φ` guard ([06 §2.3.1](06-guard-syntax-and-extensions.md))
is where the engine most visibly meets the predicate substrate. The full treatment of
how `∀`/`∃` are modeled — the three realizations, the `∀≡¬∃¬` duality, the domain model,
and decidability — is [14 — Quantification](14-quantification.md); this section is the
LogicT engine's evaluation path.

![A quantified guard, evaluated to a three-valued verdict](figures/13-quantified-eval.svg)

PlantUML source: [figures/13-quantified-eval.puml](figures/13-quantified-eval.puml).

The path, with exact symbols:

> **Algorithm `EvaluateQuantifiedGuard`.**
> ```
> where-clause source:  ∀ y ∈ nodes. entails(reachable(x,y), safe(y))
>   │  predicate_pratt.rs  (the where-clause sublanguage)
>   ▼
> BehavioralPred::Quantified { quantifier: ForAll, var: "y", domain, body }
>   │  BehavioralPred::try_to_quantified_formula()   [ast/src/language/model.rs]
>   ▼
> logict::QuantifiedFormula::forall("y", QuantifiedDomain, body)
>   │  at evaluation time
>   ▼
> evaluate_quantified(formula, env, relation_query, domain_enumerate, bound) -> bool
>   │  (theory-guided when a ConstraintTheory is registered)
>   ▼
> evaluate_quantified_with_theory(formula, theory, …) -> TriState { True, False, Unknown }
>   │  TriState::into_safe_bool()    (Unknown → false — the safe-fail collapse)
>   ▼
> Sat3 verdict (Sat | Unsat | DontKnow)  →  decidability tier  →  quality
> ```

`TriState { True, False, Unknown }` is the in-crate twin of `Sat3`
([05 §3](05-algebra-pyramid-and-decidability.md)): Kleene `∧`/`∨`/`¬`, with
`into_safe_bool` collapsing `Unknown → false`. `evaluate_quantified_with_theory`
*produces* `Unknown`: a `ForAll` returns `Unknown` when no `False` counterexample was
found but at least one sub-evaluation was `Unknown` (the `had_unknown` accumulator);
an empty domain is `True` for `∀` and `False` for `∃`. The `Unknown → false` collapse
is the sound choice — it rejects rather than wrongly admitting, the run-time mirror
of the reject-safe posture of [05 §2.1](05-algebra-pyramid-and-decidability.md) and
the Heyting / Kleene three-valued logic of [12](12-heyting-behavioral-logic.md).

> **Accuracy: where the monad is literal and where it is semantic.** Here
> `domain_enumerate` is the Rust callback that materializes a quantifier domain into a
> finite list of candidate tuples, and `multiset_partitions` is the Rust function that
> lazily streams the ways to split a bag across a set of classes (used by the
> collection algebra). The two-valued `evaluate_quantified` recurses over the
> materialized tuples from `domain_enumerate` with `all`/`any` and a `Bounded` domain's
> `min(limit, default_bound)` truncation — it does not construct a `LogicStream` per
> quantifier. The logic monad backs `TheoryAlgebra::witness` and `multiset_partitions`
> *literally* (fair search), and backs the quantifier evaluator *semantically*: the
> closed-world `∀x. φ ≡ ¬∃x. ¬φ` identity is the `gnot` equivalence, and the bounded
> enumeration mirrors `collect_bounded`. The fairness of §1 matters at the `witness`
> layer beneath a theory-guided quantifier, not in the plain enumeration.

## 4. Theory combination — the Nelson–Oppen base case

Two decidable theories over a shared enumerable domain combine into one EBA by
**joint search**: the LogicT realization interleaves their constraint streams and
labels under the bounded budget.

![Two constraint theories combine by joint interleaved search](figures/13-theory-combination.svg)

PlantUML source: [figures/13-theory-combination.puml](figures/13-theory-combination.puml).

**Result (stated; proved elsewhere).** *Two decidable constraint theories over a
shared **enumerable** domain combine into one effective Boolean algebra by exhaustive
joint search; `csat` is exact precisely because the domain enumeration is exhaustive.*
This is the **joint-search base case** of [Nelson & Oppen, 1979](references.md#nelson-oppen-1979)
— *not* the full infinite-domain equality-exchange procedure (which exchanges only
equalities over a shared signature under the stably-infinite, disjoint-signature, and
convexity hypotheses) — and the documentation says so rather than implying it. The
result, with its `eval`-homomorphism and `csat`/`cwit` soundness-and-completeness laws,
is stated and proved as
[05 — Algebra Pyramid and Decidability, Theorem 7.6](05-algebra-pyramid-and-decidability.md)
(mechanized as `combined_eba_laws`, with `csat_sound`, `csat_complete`, `cwit_sound`,
`cwit_total`, in `TheoryCombination.v`); this page does not re-prove it. The proposed
`arithmetic <+> text` syntax ([06 §3.8](06-guard-syntax-and-extensions.md)) is the
surface for it.

## 5. Enforcement of predicated types

The engine is where a quantified or theory guard earns its **tier** and **quality**,
which the fail-closed gate ([07 §5](07-language-to-rholang-integration.md)) acts on:

| How the LogicT evaluation terminates | Tier | Quality |
|---|---|---|
| finite-relation quantifier / decidable theory (propagation decides; `label = empty`) | T1 / T2 | `ExactDecidable` |
| bounded quantifier or `search_bound`-limited labeling that returned a definite verdict | T3 | `BoundedDecidable` |
| `evaluate_quantified_with_theory → Unknown` (budget exhausted, `had_unknown`), or `collect_bounded` truncated without a witness (`LT01`) | maps to `Sat3::DontKnow` | fail-closed unless asserted (`#[tier(t4)]` / `@[quality(trusted)]`) |
| Z3/SMT gap-filler (feature `smt`, §2.1) decides via `is_satisfiable_3v` + a certificate-checked witness; `Sat`/`Unsat` are definite, an `unknown` is `DontKnow` | T3 (T4 on `unknown`) | `BoundedDecidable` (reject-safe on `DontKnow`) |

Two places turn the engine's "don't know" into a *rejection*, never a false
admission: `into_safe_bool` (`Unknown → false`) and the bridge's
`is_satisfiable = witness().is_some()`. Both are the operational realization of the
reject-safe discipline ([05 §5](05-algebra-pyramid-and-decidability.md)). The
governing soundness result — *the asymmetric mixed De Morgan complement
`(¬a ∧ ⊤) ∨ (⊤ ∧ ¬b)` of a structural-times-behavioral guard accepts an element only
if the true product `a ∧ b` rejects it, so a guarded action can never fire when its
complement holds* — is stated and proved as
[12 — Heyting Behavioral Logic, Theorem 6.1](12-heyting-behavioral-logic.md)
(mechanized as `mixed_negation_soundness` in `BehavioralNegation.v`, with the run-time
mirror `rho_complement_no_commit` in `RhoGuardedCommSoundness.v`); this page does not
re-prove it. The two rejection sites connect directly to `classify_quality` — the
Rust classifier (defined in [07 §4.3](07-language-to-rholang-integration.md)) that maps
a guard's obligation and disposition to a quality grade — whose
`behavioral → reject-safe` rule the flip gate then acts on alongside its block on
`Unknown`. The decidability-tier lattice
([05 §6](05-algebra-pyramid-and-decidability.md), the tier ↔ regularity correspondence
of [12 — Heyting Behavioral Logic, Proposition 6.3](12-heyting-behavioral-logic.md),
mechanized as `GuardTierCertificate.v`) is the formal frame;
`collect_bounded(search_bound)` plus the `LT01` lint is the resource meter that decides
which tier a given guard lands in.

## 6. Accuracy corrections

Two divergences between the idealized description and the live code, recorded for a
reader tracing the integration:

1. **A codegen-to-API drift in the quantifier shorthand.** The macro codegen
   (`ast/src/language/model.rs`, `macros/src/gen/runtime/wpda_codegen/refinement.rs`)
   emits constructor shorthands `nforall` / `nexists` / `natom` / `nand` / `nor` /
   `nnot` / `nimplies` / `nn` / `nmultiset_partitions`. **None of these resolve in
   `prattail/src/`** — the real public API is `QuantifiedFormula::{forall, exists,
   atom, and, or, not, implies}`, `evaluate_quantified`, and `multiset_partitions`.
   This document uses the real API; the shorthand layer is a codegen reference that
   does not correspond to a present `prattail` symbol.
2. **Three different `QuantifiedDomain` shapes.** The AST `BehavioralPred::Quantified`
   carries `domain: Option<Ident>` plus a separate `bound: Option<usize>`; the runtime
   `BehavioralPred` carries `domain: Option<QuantifiedDomain>` with variants
   `Named | Bounded(usize) | Enumerated`; the `logict::QuantifiedDomain` is
   `Relation(String) | Bounded { relation, limit }`. A reader should not assume one
   type; the lowering bridges them.

## 7. The mechanized and reference account

Each named result below is **stated and proved in its proof-home document**; this
table is the citation index, not a second proof site. The Coq names appear only as the
mechanizing witnesses of the cited theorems.

| Claim | Stated-and-proved in | Coq witness |
|---|---|---|
| theory combination is an EBA (Nelson–Oppen joint-search base case) | [05 — Theorem 7.6](05-algebra-pyramid-and-decidability.md) | `combined_eba_laws`, `csat_sound`, `csat_complete`, `cwit_sound`, `cwit_total` (`TheoryCombination.v`) |
| the mixed-guard complement is reject-safe (a covered theory guard never false-fires) | [12 — Theorem 6.1](12-heyting-behavioral-logic.md) | `mixed_negation_soundness` (`BehavioralNegation.v`); run-time mirror `rho_complement_no_commit` (`RhoGuardedCommSoundness.v`) |
| the tier ↔ regularity / decidability frame the engine populates | [12 — Proposition 6.3](12-heyting-behavioral-logic.md) ([05 §6](05-algebra-pyramid-and-decidability.md) summary) | `tier_max_sound_hom`, `tier_regularity_reg`, `tier_regularity_boundary`, `tier_regularity_closed` (`GuardTierCertificate.v`) |
| the Z3/SMT witness is certificate-checked, never fabricated — the soundness fence on the `Sat3`-only backend (§2.1) | [10 §2.1](10-formal-verification-and-tests.md) | `checked_witness_sound`, `checked_witness_no_fabrication` (`Z3WitnessChecked.v`) |
| the consolidated proof ledger for all three rows above | [10 §2.1](10-formal-verification-and-tests.md) | — |
| the bounded-search lint | `prattail/docs/diagnostics/logict/LT01.md` | `logict-search-bound-exceeded` |
| full API + algorithms (`msplit`, `interleave`, `fair_conjoin`, `witness`, `evaluate_quantified`) | `prattail/docs/design/constraint-theories/logict-framework.md` | — |

The engine is cited from [Kiselyov et al., 2005](references.md#kiselyov-2005)
(the LogicT monad and its fair operators) and [Hemann & Friedman, 2013](references.md#hemann-friedman-2013)
(the relational-programming lineage), with the combination grounded in
[Nelson & Oppen, 1979](references.md#nelson-oppen-1979).

## 8. Cross-references

- The abstract algebra the engine realizes: [02 — Effective Boolean Algebra](02-effective-boolean-algebra.md)
  (the `TheoryAlgebra` instance and the `BooleanAlgebra` trait it implements).
- The tiers, `Sat3`, reject-safety, and the closure family it feeds:
  [05 — Algebra Pyramid and Decidability](05-algebra-pyramid-and-decidability.md).
- The guard syntax that builds the formulas: [06 — Guard Syntax and Extensions](06-guard-syntax-and-extensions.md)
  (quantifiers §2.3.1 / §3.1, theory combination §3.8).
- The classification and fail-closed gate the engine feeds:
  [07 — Language-to-Rholang Integration](07-language-to-rholang-integration.md).
- The three-valued / Kleene logic the `TriState` realizes:
  [12 — Heyting Behavioral Logic](12-heyting-behavioral-logic.md).
- The deep engine reference and the proof matrix:
  `prattail/docs/design/constraint-theories/logict-framework.md` and
  [10 — Formal Verification and Tests](10-formal-verification-and-tests.md).
