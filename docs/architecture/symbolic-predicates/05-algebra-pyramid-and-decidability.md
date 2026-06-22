# Algebra Pyramid and Decidability

Last updated: 2026-06-22

All symbols are defined in [Concepts and Glossary](01-concepts-and-glossary.md).
This document is the conceptual heart of the substrate: the **algebra tower** that
keeps a semi-decidable behavioral algebra from ever being mistaken for a classical
one, the three-valued satisfiability and decidability tiers that quantify "how
decidable" a guard is, and the **closure family** that extends the whole framework
to every data type a `language!` can declare.

## 1. The problem the tower solves

[02 — Effective Boolean Algebra](02-effective-boolean-algebra.md) presented the
classical `BooleanAlgebra` trait: an involutive complement `¬` with `¬¬a = a`, and
a two-valued `is_satisfiable`. That is exactly right for **structural** predicates
— predicates over the *shape* of data (a constructor pattern, an interval, a
character class). Their satisfiability is decidable and their complement is exact.

It is exactly **wrong** for **behavioral** predicates — predicates over the
*dynamics* of a process, such as "does `P` halt?", "is `P` safe?", or a
modal/temporal property `AG φ`. These are only **semi-decidable**: a bounded
search can find a witness (proving satisfiability) but a budget-exhausted "no
witness found" is **not** a proof of unsatisfiability. Treating such an algebra
classically would let `¬(reachable)` be asserted from a failed bounded search —
an unsound complement that could wrongly *admit* a communication.

> **The danger, concretely.** If a behavioral algebra exposed a classical `not`,
> then an SFA `complement` or `determinize` over it would compute `¬φ` by "the
> states where `φ` failed within budget" — silently converting *don't-know* into
> *false*. A guard built on that complement could fire on a process that does
> **not** actually satisfy it.

The tower removes the danger by **type**: a semi-decidable algebra simply does not
have the classical operations, so no algorithm bounded on `BooleanAlgebra` can be
instantiated over it.

![The algebra tower: trait refinement and the strength lattice](figures/05-algebra-tower.svg)

PlantUML source: [figures/05-algebra-tower.puml](figures/05-algebra-tower.puml).

## 2. The three tiers

The tower is realized in `prattail/src/algebra_tower.rs` as three traits, weakest
to strongest:

| Tier | Trait | Operations | Laws |
|---|---|---|---|
| weakest | `RejectSafeAlgebra` | `and`, `or`, `pseudo_complement`, `is_satisfiable_3v → Sat3` | SAT-soundness, double-negation-soundness. **No involutive complement, no excluded middle.** |
| middle | `HeytingAlgebra : RejectSafeAlgebra` | adds `implies` (`→`, the right adjoint of `∧`) and `regularize` (`¬¬`) | intuitionistic implication; `¬¬a = a` only on *regular* elements |
| strongest | `BooleanAlgebra` (the classical tier from [02](02-effective-boolean-algebra.md)) | involutive `not`, 2-valued `is_satisfiable` | full Boolean algebra; excluded middle |

Read the containment as *strength of available reasoning*: a `BooleanAlgebra` can
do everything a `HeytingAlgebra` can, which can do everything a `RejectSafeAlgebra`
can. The strength order is a lattice; the figure draws it as a Hasse diagram beside
the trait-inheritance view.

> **Definition 2.1 (Reject-safe).** A decision procedure is *reject-safe* when it
> may **reject** a satisfiable element but **never admits** an unsatisfiable one.
> Formally, for a guard `φ` and element `e`: `decide(φ, e) = admit ⇒ e ⊨ φ`. The
> converse need not hold — a satisfiable `e` may be rejected when the bounded
> search is inconclusive. This is the only sound posture for a semi-decidable
> predicate, and it is the contract `RejectSafeLaws` proves in
> `EffectiveBooleanAlgebra.v` (with `eba_implies_reject_safe`: every classical EBA
> is in particular reject-safe).

## 3. Three-valued satisfiability (`Sat3`)

A classical `is_satisfiable` returns `bool`. A semi-decidable one must be allowed
to say "I could not determine this within budget." That third answer is `Sat3`:

```rust
pub enum Sat3 { Sat, Unsat, DontKnow }
```

`Sat3` carries Kleene three-valued `∧`/`∨`/`¬` and an `into_safe_bool` that maps
`DontKnow → None` (so a caller must *handle* the uncertainty rather than
accidentally coerce it to `false`). A classical algebra lifted into the tower only
ever produces `Sat`/`Unsat`; a genuinely semi-decidable algebra (for example
`BehavioralAlgebra`, a closed-world CTL model over a `FactBase`) produces
`DontKnow` precisely when a bounded reachability search neither found a witness nor
proved emptiness.

> ⚠ **Citation caveat.** `Sat3` is a **Rust** enum (`algebra_tower.rs`); it is
> **not** a Coq object, and there is no `Sat3` or `Esakia` lemma to cite. The
> mechanized account of three-valued behavior is the `TriModel` module in
> `BehavioralNegation.v` (`excluded_middle_fails`, `no_classical_complement`,
> `tri_neg_sound`) together with the regular-element results in `HeytingAlgebra.v`
> (`neg_involutive_on_regular`, `excluded_middle_reg`). See
> [10 — Formal Verification](10-formal-verification-and-tests.md).

## 4. Realization: non-invasive lifting

The tower had to be added **without** touching the ~13 existing `BooleanAlgebra`
implementors and **without** introducing method-name ambiguity on the many
unqualified `.and()`/`.or()` calls in the existing combinators. The design that
achieves both:

- A classical algebra is lifted into the reject-safe / Heyting tiers by wrapping
  it in `Classical<A>`, whose impls *delegate* to the classical operations:
  `pseudo_complement = not`, `regularize = id`, `is_satisfiable_3v` only ever
  `Sat`/`Unsat`, `implies = ¬a ∨ b`.
- A genuinely semi-decidable algebra implements `HeytingAlgebra` **directly and
  does not implement `BooleanAlgebra`**.

The consequence is the **load-bearing safety property**:

> **Property 4.1.** Any operation bounded on `BooleanAlgebra` — every SFA
> `complement`, `determinize`, and exact `is_equivalent` — is *statically
> unavailable* on a semi-decidable algebra. Attempting to use it does not
> type-check.

This is verified by a `compile_fail` doctest on `RejectSafeProduct` in
`algebra_tower.rs`: the test *asserts that the code fails to compile*, turning the
safety property into a checked artifact rather than a convention.

## 5. The mixed guard: structural × behavioral

Most real guards are *both* structural and behavioral — for example "the message
matches pattern `P` **and** the sender `halts`." The combined algebra is
`RejectSafeProduct<S, B>`, where `S` is a classical structural algebra and `B` a
semi-decidable behavioral one. It is `RejectSafeAlgebra` **only** (never
`BooleanAlgebra`, by Property 4.1, since one leg is semi-decidable), and its
pseudo-complement is the **asymmetric De Morgan** law:

`¬(a ∧ b) = (¬a ∧ ⊤) ∨ (⊤ ∧ ¬b)`

where `¬a` is the *exact* structural complement and `¬b` is the *reject-safe*
behavioral pseudo-complement. The result is a proven **reject-safe
over-approximation** of the true complement: it may reject more than necessary but
never admits a non-member.

> **Theorem 5.1 (Mixed-negation soundness).** For the mixed guard `a ∧ b`, the
> asymmetric complement `(¬a ∧ ⊤) ∨ (⊤ ∧ ¬b)` accepts an element only if the true
> product `a ∧ b` rejects it. Mechanized as `mixed_negation_soundness` in
> `BehavioralNegation.v` (with `mixed_guard_no_false_fire`); zero-admission.

The practical payoff: a language may freely mix structural and behavioral guards
and still get a *sound* (reject-safe) compile-time analysis — never a false fire —
which is exactly what the integration in
[07 — Language-to-Rholang Integration](07-language-to-rholang-integration.md)
requires before it will admit the language.

## 6. Decidability tiers

Orthogonal to the algebra tier (which is about *available operations*) is the
**decidability tier**, which classifies a guard by *when* it can be decided:

| Tier | `DecidabilityTier` | `GuardTier` (Rho mirror) | Meaning |
|---|---|---|---|
| T1 | `CompileTimeDecidable` | `T1Exact` | decided entirely at compile time (pure structure / constants) |
| T2 | `RuntimeDecidable` | `T2Decidable` | decidable, but needs the runtime value |
| T3 | `SemiDecidable` | `T3Bounded` | decidable only up to a bound (reachability within budget) |
| T4 | `Undecidable` | `T4Asserted` | not decidable; must be trusted/asserted or host-observed |

The tier of a *combined* guard is the **weakest leg**: `tier(a ∧ b) = max(tier a,
tier b)` under the order `T1 ≤ T2 ≤ T3 ≤ T4`. This `max_tier` operation is a
join-semilattice, and combination is a **homomorphism** into it — a guard built
from sub-guards has exactly the tier the lattice predicts.

> **Theorem 6.1 (Tier lattice).** `(tier, max_tier)` is a join-semilattice
> (`tier_max_comm`, `tier_max_idem`, `tier_max_assoc`, with `tier_max_ub_l`,
> `tier_max_ub_r`, `tier_max_least`), and combination is sound and complete with
> respect to it (`tier_max_sound_hom`, `tier_max_complete_hom`, `tier_max_exact`).
> The tier↔regularity correspondence (`tier_regularity_reg`,
> `tier_regularity_boundary`, `tier_regularity_closed`) ties the lattice to the
> Heyting regular elements of §2. All in `GuardTierCertificate.v`; zero-admission.

The tier drives the **quality** grade the backend consumes (T1 and T2 yield exact,
T3 yields bounded, T4 yields trusted), detailed in
[07 — Language-to-Rholang Integration](07-language-to-rholang-integration.md).

## 7. Closing the family under type constructors

A `language!` declares arbitrary data types — tuples, variants, lists, bags, maps,
recursive trees. The substrate covers *all* of them not by writing new automata
but by **closing the EBA family under a small set of constructors**, each of which
is itself a `BooleanAlgebra` (or reject-safe algebra), so the SFA/SFT code and the
algebra-agnostic proofs of [10](10-formal-verification-and-tests.md) apply verbatim.

![The closure family: each constructor is itself an algebra](figures/05-closure-family.svg)

PlantUML source: [figures/05-closure-family.puml](figures/05-closure-family.puml).

| Constructor | Algebra | Predicate intuition | Closure proof |
|---|---|---|---|
| product (tuple/record) | `NaryProductAlgebra<A>` | a rectangle in `D_A × D_B × …`; complement is a DNF of rectangles | `ProductAlgebraClosure.v` (`product_eba_laws`) |
| sum (variant/alternation) | `SumAlgebra<A>` | a tagged choice; project into a summand | `SumAlgebraClosure.v` (`sum_eba_laws`) |
| collection (bag) | `BagAlgebra<A>` | a per-minterm occupancy-count vector | `CollectionAlgebraClosure.v` |
| collection (map) | `MapAlgebra<K,V>` | key × value counts + distinct-key cap | `CollectionAlgebraClosure.v` |
| sequence (list) | `ListAlgebra<A>` = `RegexAlgebra<A>` | an ordered language, recognized by an SFA | `CollectionAlgebraClosure.v` |
| recursive tree | `TreeAlgebra<A>` | "constructor `c` ∧ payload ⊨ `φ` ∧ childᵢ ⊨ `φᵢ`" | `TreeAlgebraClosure.v` (`tree_eba`) |
| theory combination | `TheoryAlgebra` (union) | two decidable theories over a shared domain | `TheoryCombination.v` (`combined_eba_laws`) |

The complement of a collection or tree predicate uses the SFA **minterms** of
[02 §4](02-effective-boolean-algebra.md): every element falls in exactly one
minterm, so a collection is characterized by its per-minterm count vector and a
tree by its bottom-up acceptance. **First-order pattern matching is subsumed**: a
pattern lowers to a `TreePred<AnyAlgebra>` (constructor node + `Var` wildcards +
symbolic payload guards), and `match P t ⟺ TreeAlgebra.evaluate(toTreePred(P),
toSymTerm(t))`; inhabitation is `is_satisfiable`, and `witness` even yields a
sample matched term the bespoke matcher cannot.

> **Theory combination is the Nelson–Oppen base case.** `TheoryCombination.v`
> proves two decidable theories over a shared enumerable domain combine into an
> EBA via joint search (`csat_sound`, `csat_complete`); the full
> equality-exchange refinement of [Nelson & Oppen, 1979](references.md#nelson-oppen-1979)
> is out of scope, and the document says so rather than implying it.

## 8. The carrier that holds it all

All of these instances unify under the single closed-enum carrier `AnyAlgebra`
([02 §6](02-effective-boolean-algebra.md)), so a tree node's heterogeneous
children share one `Predicate`/`Domain` type and the whole family drops into the
automata by `match` dispatch with no `dyn` and no allocation in the hot path. The
`SortRegistry::from_grammar` derives the per-language family from the declared
`NativeKind`s and grammar categories — the boundary contract that
[07](07-language-to-rholang-integration.md) builds on.

## 9. Summary — what the tower guarantees

1. **Soundness by type.** A semi-decidable behavioral algebra cannot be used where
   a classical one is required; the `complement`/`determinize`/`equivalence`
   algorithms are statically unavailable on it (Property 4.1).
2. **Reject-safety end to end.** Mixed structural × behavioral guards complement by
   asymmetric De Morgan and are proven never to fire falsely (Theorem 5.1).
3. **Quantified decidability.** Every guard carries a tier; combination is a proven
   join-semilattice homomorphism (Theorem 6.1), and the tier sets the quality the
   backend gates on.
4. **Every data type, one library.** The family is closed under product, sum,
   collection, tree, and theory combination, each itself an algebra, so the
   automata and the proofs are reused unchanged.
