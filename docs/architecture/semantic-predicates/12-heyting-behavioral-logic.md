# Heyting Algebras for Behavioral Constraints

Last updated: 2026-06-22

All symbols are defined in [Concepts and Glossary](01-concepts-and-glossary.md).
This is the theoretical treatise behind a claim that
[05 — Algebra Pyramid and Decidability](05-algebra-pyramid-and-decidability.md)
states as engineering: the tower `RejectSafeAlgebra ⊂ HeytingAlgebra ⊂ BooleanAlgebra`.
Document 05 summarizes *that* the behavioral tier is a Heyting algebra; this document
**argues why a Heyting algebra is the mathematically correct — not merely convenient
— home for behavioral guards**, why that is non-obvious, how it **completes** Boolean
algebra for full structural-behavioral predicate types, how **bisimulation** makes
behavioral predicates well-defined, and why it **aligns with OSLF**. It is the
logic-of-guards argument; it does not re-derive the EBA
([02](02-effective-boolean-algebra.md)), the closure family
([05 §7](05-algebra-pyramid-and-decidability.md)), or run-time enforcement
([08](08-runtime-comm-enforcement.md)).

> ⚠ **Citation caveat.** `Sat3` and `Esakia` are **not** Coq objects. `Sat3` is the
> Rust enum in `algebra_tower.rs`; Esakia duality and the Brouwer–Heyting–Kolmogorov
> reading are discussed here as *theory* — the intellectual basis — with literature
> citations, never as a mechanized lemma. Every mechanized claim is carried by
> `HeytingAlgebra.v`, `BehavioralNegation.v`, and `GuardTierCertificate.v`. This
> document reuses the suite color legend, with **green** carrying the sense "regular
> element = recovered-classical."

## 1. The thesis, and why it is non-intuitive

Heyting algebras were born in three places that have nothing to do with concurrency
or resources: **intuitionistic logic** (Heyting's 1930 algebraization of Brouwer's
intuitionism, [Heyting, 1930](references.md#heyting-1930)); **topology** (the lattice
of open sets `O(X)` of any space is a Heyting algebra — the canonical model of
intuitionistic propositional logic, [Johnstone, 1982](references.md#johnstone-1982));
and **topos theory** (the subobject classifier of any topos carries a Heyting
structure, [Mac Lane & Moerdijk, 1992](references.md#maclane-moerdijk-1992)). None of
these is a resource logic. OSLF, by contrast, is an ordered linear-substructural
*funding* discipline ([09](09-oslf-composition.md)). Importing a Heyting algebra to
govern behavioral guards *inside a resource logic* therefore crosses two unrelated
traditions, and a reader is right to demand an argument rather than an analogy.

![A small non-Boolean Heyting algebra: the three-element chain where `¬¬M ≠ M`](figures/12-heyting-hasse.svg)

PlantUML source: [figures/12-heyting-hasse.puml](figures/12-heyting-hasse.puml).

> **Thesis.** The natural logic of *observable / provable behavioral properties*
> over a transition system is **intuitionistic**, and its algebra is therefore a
> **Heyting algebra** — not by stylistic preference but because behavioral predicates are
> *semi-decidable*, and semi-decidability is exactly the structure that intuitionistic
> logic, via the Brouwer–Heyting–Kolmogorov reading, axiomatizes. Classical Boolean
> logic is the *special case* recovered on the decidable (structural) fragment — the
> regular elements. Hence Heyting **completes** Boolean for a predicate type that must
> carry both structural and behavioral guards.

The two classical assumptions that fail are **excluded middle** `a ∨ ¬a = ⊤` and
**involutive complement** `¬¬a = a`. Both encode determinacy — "every proposition is
settled true or false." A semi-decidable predicate is precisely one for which
determinacy is not available *as evidence*. The argument proceeds: §2 the
mathematics; §3 the evidence argument (BHK and topology); §4 bisimulation as the
well-definedness of behavioral predicates; §5 the completion; §6 the OSLF affinity;
§7 a worked example; §8 the mechanized account.

## 2. The mathematics of Heyting algebras

> **Definition 2.1 (Bounded lattice).** `(H, ∧, ∨, ⊤, ⊥)` with commutative,
> associative, idempotent `∧` and `∨` satisfying absorption, with `⊤` the top and `⊥`
> the bottom (`meet_top`, `join_bot`). The order is `a ≤ b :⟺ a ∧ b = a`; it is a
> partial order with `∧` the greatest lower bound (`le_refl`, `le_antisym`,
> `le_trans`, `meet_glb_l`, `meet_glb_r`, `meet_greatest` in `HeytingAlgebra.v`).

> **Definition 2.2 (Heyting algebra).** A bounded lattice with a binary **Heyting
> implication** `→` characterized by the adjunction
> `c ∧ a ≤ b ⟺ c ≤ (a → b)` — that is, the meet functor is left adjoint to
> implication, `(a ∧ —) ⊣ (a → —)` (Coq `himp_adj`). The **pseudo-complement** is
> `¬a := a → ⊥` (Coq `hneg`).

![The adjunction `(a ∧ —) ⊣ (a → —)` that defines Heyting implication](figures/12-adjunction.svg)

PlantUML source: [figures/12-adjunction.puml](figures/12-adjunction.puml).

The adjunction is the whole content: implication is exactly as strong as it must be.
Its counit is modus ponens, `a ∧ (a → b) ≤ b` (`imp_counit`), sharpened to
`a ∧ (a → b) = a ∧ b` (`imp_meet`).

### 2.1 The laws that distinguish Heyting from Boolean

| Law | Boolean (`EffectiveBooleanAlgebra.v`) | Heyting (`HeytingAlgebra.v`) |
|---|---|---|
| non-contradiction `a ∧ ¬a = ⊥` | `non_contradiction` (holds) | holds |
| **excluded middle** `a ∨ ¬a = ⊤` | `excluded_middle` (holds) | **fails in general**; recovered only as `a ⊔ ¬a = ⊤` for the Boolean join `⊔` (`excluded_middle_reg`) |
| **double negation** `¬¬a = a` | `double_neg` (holds) | **only `a ≤ ¬¬a`** (`dneg_extensive`); the converse fails |
| triple negation `¬¬¬a = ¬a` | trivial | `neg_triple` |
| `¬¬` idempotent `¬¬¬¬a = ¬¬a` | trivial | `dneg_idempotent` |
| De Morgan `¬(a ∨ b) = ¬a ∧ ¬b` | holds | holds |
| De Morgan `¬(a ∧ b) = ¬a ∨ ¬b` | `de_morgan_conj` (both ways) | **one direction only** |

This table is the technical core, and the **asymmetry of the two De Morgan laws is
load-bearing**: `¬(a ∨ b) = ¬a ∧ ¬b` survives intuitionistically, but
`¬(a ∧ b) = ¬a ∨ ¬b` does not. That is *exactly why* the mixed-guard complement of
§5 must use a padded, double-`⊤` asymmetric form rather than a plain `¬a ∨ ¬b`.

### 2.2 Double negation is a closure operator

`¬¬` is **extensive** (`a ≤ ¬¬a`, `dneg_extensive`), **monotone** (`dneg_mono`), and
**idempotent** (`¬¬¬¬a = ¬¬a`, `dneg_idempotent`) — the three defining properties of a
closure operator. The triple-negation law `¬¬¬a = ¬a` (`neg_triple`) is the
antitone collapse that powers it. Its soundness payoff is `dneg_eq_bot_implies_bot`
(`¬¬a = ⊥ ⇒ a = ⊥`): a sound complement never drops a satisfiable predicate.

### 2.3 The regular elements: the Booleanization

The fixed points of the closure operator are the **regular elements**
`H_reg := { a : ¬¬a = a }` (Coq `regular`). They form a Boolean algebra — the
**Booleanization** of `H` — and this is the precise sense in which "classical
reasoning is sound exactly on the decidable fragment." The cluster of results:

- every `¬a` is regular (`neg_regular`, via `neg_triple`);
- `⊥` and `⊤` are regular (`regular_bot`, `regular_top`);
- `H_reg` is closed under `∧` (`regular_meet`);
- on `H_reg`, `¬` is involutive (`neg_involutive_on_regular`);
- excluded middle holds for the **Boolean join** `a ⊔ b := ¬(¬a ∧ ¬b)` (Coq `bjoin`):
  `a ⊔ ¬a = ⊤` (`excluded_middle_reg`).

> **Accuracy note (the Boolean join).** `excluded_middle_reg` is stated for `⊔` (the
> double-negation / De Morgan join `bjoin`), **not** the lattice join `∨`. With the
> ordinary `∨`, `a ∨ ¬a = ⊤` still fails in general (the `Chain3` model has
> `M ∨ ¬M = M ∨ ⊥ = M ≠ ⊤`). The precise statement is: *the regular elements form a
> Boolean algebra under `(∧, ⊔, ¬)`, and excluded middle holds for `⊔`.* The
> historical name for "the regular elements Booleanize `H`" is Glivenko's theorem.

![The regular elements form a Boolean algebra embedded inside the Heyting algebra](figures/12-booleanization.svg)

PlantUML source: [figures/12-booleanization.puml](figures/12-booleanization.puml).

The slogan: *the regular elements are exactly where classical reasoning is sound; the
gap `¬¬a` above `a` is the indeterminate region.* In code, lifting a classical
algebra with `Classical<A>` makes `regularize = id` (`algebra_tower.rs`) — everything
is regular, the all-classical special case.

### 2.4 The topological and Kripke models

The intuition for `observable ⇒ open ⇒ intuitionistic` is the **topological model**.
In `O(X)`, `∧ = ∩`, `∨ = ∪`, `⊤ = X`, `⊥ = ∅`, and negation is the **interior of the
set-complement**, `¬U = int(X ∖ U)`. Then `¬¬U = int(cl(U))` is the *regularization*
of `U`, and `U` is regular exactly when it is a **regular-open** set (`U = int(cl(U))`).
Excluded middle `U ∪ ¬U = X` fails precisely when `U` has nonempty boundary — and the
boundary `∂U` is the topological avatar of "indeterminate."

![Intuitionistic negation as interior: the boundary is the indeterminate region](figures/12-negation-as-interior.svg)

PlantUML source: [figures/12-negation-as-interior.puml](figures/12-negation-as-interior.puml).

Equivalently, the **Kripke model**: intuitionistic truth is a *monotone (persistent)*
valuation over a poset of states of knowledge — once true, true under more
information. This is the exact analog of a closed-world fact base that only *grows*
(`behavioral_algebra.rs` adds facts, never retracts; the reachable transition set only
grows). The duality-theoretic underpinning is **Esakia duality** (Heyting algebras are
dual to Esakia spaces, the Heyting analog of Stone duality for Boolean algebras,
[Esakia, 2019](references.md#esakia-2019)) — stated here as the conceptual frame
only; no `Esakia` lemma is mechanized.

## 3. Why behavioral = semi-decidable = intuitionistic

This is the central argument. Behavioral predicates — reachability, modal/temporal
safety and liveness over a labeled transition system (LTS) — are **semi-decidable**: a
bounded search can *witness* truth but a failed search is *not* a proof of falsehood.
This is concrete in the code:

- `BehavioralAlgebra::is_satisfiable_3v` returns `Sat3::DontKnow` for any modal
  formula, because modal satisfiability is semi-decidable without a full μ-calculus
  satisfiability engine; the model-checking direction (`evaluate` against a *given*
  process) is exact but bounded by `MAX_REACH_STATES`, and the truncation is
  reject-safe ("missing edges only shrink modal satisfaction sets").
- relational satisfiability searches the assignment space and returns `DontKnow` on
  budget exhaustion (`DEFAULT_SEARCH_BUDGET`).

So the third truth value is *structural*, not sloppy: it is the honest report of an
incomplete search. Asserting `¬φ` from "no witness found within budget" would convert
*don't-know* into *false* — the unsound complement the tower forbids
([05 §1](05-algebra-pyramid-and-decidability.md)). Algebraically that refusal is
visible as `Sat3::DontKnow.not() = DontKnow` (three-valued negation has `DontKnow` as
a fixed point), while `into_safe_bool` maps `DontKnow` to `None`, forcing the caller to
*handle* indeterminacy rather than coerce it to `false`.

### 3.1 The Brouwer–Heyting–Kolmogorov reading

Under the BHK interpretation ([Troelstra & van Dalen, 1988](references.md#troelstra-vandalen-1988)),
a proposition is interpreted by its **proofs / evidence**:

- a proof of `a ∧ b` is a pair of proofs; of `a ∨ b`, a tagged proof of one side; of
  `a → b`, a method transforming proofs of `a` into proofs of `b`;
- a proof of `¬a := a → ⊥` is **a method turning any proof of `a` into a
  contradiction** — *refuting evidence*, strictly stronger than "we failed to find a
  witness for `a`."

For semi-decidable behavioral predicates this reading is *literal*: "we have a
witness" is a proof of `φ`; "we have a refutation" is a proof of `¬φ`; and an
inconclusive bounded search has **neither**, so neither `φ` nor `¬φ` is assertible and
`φ ∨ ¬φ` is not a theorem. **That is the failure of excluded middle, derived from
first principles about evidence** — which is why the Heyting application is correct,
not an ad-hoc contrivance. The natural logic of observable behavioral properties is intuitionistic,
and its Lindenbaum–Tarski algebra is a Heyting algebra.

### 3.2 The correspondence, made precise

| Intuitionistic / topological notion | Behavioral-substrate realization |
|---|---|
| open set / observable property | semi-decidable behavioral predicate (a witness is a finite observation) |
| `¬U = int(X ∖ U)` (negation as interior) | reject-safe `pseudo_complement`: assert the complement only on *refuting* evidence |
| boundary `∂U` (where `U ∪ ¬U ≠ X`) | the `Sat3::DontKnow` region — bounded search inconclusive |
| regular-open `U = int(cl(U))` (`¬¬U = U`) | the decidable / structural fragment — classical reasoning recovered |
| persistent (monotone) Kripke valuation | the closed-world fact base / reachable LTS that only grows |
| `no proof ⇒ no assertion` | reject-safety: never grant on absence of evidence ([05 Def 2.1](05-algebra-pyramid-and-decidability.md)) |

### 3.3 The mechanized witness that excluded middle fails

`BehavioralNegation.v`'s `Module TriModel` is the concrete three-valued model. Its
carrier is `{ TSat, TUnsat, TUnknown }` with `tri_eval(TUnknown) = false` and
`tri_neg(TUnknown) = TUnknown`. Then `excluded_middle_fails` exhibits `TUnknown`
satisfying neither `p` nor `¬p`; `no_classical_complement` shows
`tri_eval p ∨ tri_eval (¬p) = false` at `TUnknown`; and `tri_neg_sound` confirms the
negation is reject-safe (`¬p` accepts ⇒ `p` rejects). This zero-admission model
realizes the abstract failure *and* discharges the abstract hypotheses of the
`MixedNegation` section, proving them consistent. Its Rust mirror is `TriAlg` in
`algebra_tower.rs` — `Tri::Unknown` is the `Sat3::DontKnow` region.

> **Where the non-classicality actually lives.** In the *idealized* algebra the
> non-classicality is visible as `¬¬a ≠ a` (the `Chain3` model: `¬¬M = ⊤ ≠ M`). In the
> *running* `BehavioralAlgebra`, the syntactic `pseudo_complement` smart constructor
> collapses `¬¬φ` to `φ`, so the intuitionistic character is **not** carried by a
> syntactically non-involutive `¬`. It is carried by the **three-valued,
> snapshot-relative, budget-bounded denotation**: `is_satisfiable_3v` returns
> `DontKnow` exactly on the boundary, and the closed-world fact base only grows. The
> two presentations are the same logic seen two ways — the algebraic `¬¬a ≠ a` of
> `Chain3`/`TriModel`, and the operational `Sat3::DontKnow` of the live algebra. A
> reader must not expect to *see* `¬¬φ ≠ φ` by printing a behavioral formula; the
> indeterminacy shows up when the predicate is *decided*, not when it is *built*.

## 4. Bisimulation: behavioral predicates are observational

A behavioral predicate is a property of *behavior*, not *representation*. Two
processes that are observationally indistinguishable must satisfy the same behavioral
guards — otherwise a guard would depend on syntactic accidents the calculus deems
irrelevant. The equivalence that captures "observationally indistinguishable" is
**bisimulation**, and bisimulation-invariance is the **well-definedness condition** for
behavioral predicates. This section makes that precise and ties it back to the
intuitionistic frame of §2–§3.

> **Definition 4.1 (Bisimulation).** Over an LTS `(S, →)`, a relation `R ⊆ S × S` is a
> **bisimulation** when, for all `(p, q) ∈ R`: (i) every step `p → p′` is matched by a
> step `q → q′` with `(p′, q′) ∈ R`, and (ii) symmetrically every `q → q′` is matched
> by some `p → p′` with `(p′, q′) ∈ R`. States `p` and `q` are **bisimilar**, written
> `p ∼ q`, when some bisimulation relates them. Bisimilarity `∼` is itself the largest
> bisimulation — a greatest fixed point.

The repository realizes this on both sides. The compile-time implementation is
`prattail/src/bisimulation.rs`, described in its own module documentation as "the
compile-time layer of the **Heyting-SFA bisimilarity**": it computes the **coarsest
bisimulation refining an initial coloring** by partition refinement over a behavioral
LTS, with `Lts::bisimilar(s, t, initial_colors)` deciding `s ∼ t` and
`Lts::is_bisimulation(blocks, colors)` checking a candidate partition (matching
transitions both ways, same initial color). The mechanized account is
`formal/rocq/advanced_automata/theories/RegisterEquivalence.v`, which defines
`bisimulation` and `bisimilar` and proves `self_bisimilar` (reflexivity, `∼` is itself
a bisimulation) and `fixed_point_is_bisimulation` (the fixed point of the refinement is
a genuine bisimulation), with a `bisim_space_bound` for the partition-refinement
search.

![Bisimulation invariance: two bisimilar processes satisfy the same behavioral predicate](figures/12-bisimulation-invariance.svg)

PlantUML source: [figures/12-bisimulation-invariance.puml](figures/12-bisimulation-invariance.puml).

### 4.1 Hennessy–Milner: modal logic *is* the bisimulation-invariant logic

The link between behavioral *logic* and bisimulation is the **Hennessy–Milner
theorem**: over an image-finite LTS, two states satisfy the same modal formulas if and
only if they are bisimilar ([Hennessy & Milner, 1985](references.md#hennessy-milner-1985)).
Its model-theoretic companion is the **van Benthem characterization**: modal logic is
exactly the bisimulation-invariant fragment of first-order logic
([van Benthem, 1983](references.md#van-benthem-1983)). Together they say the modal /
behavioral formulas are *precisely* the predicates that cannot tell bisimilar processes
apart — they are the well-defined behavioral predicates, and nothing more.

> **Theorem 4.2 (behavioral predicates are bisimulation-invariant).** If `φ` is a
> behavioral (modal/temporal) predicate built from the operators of
> `behavioral_algebra.rs` (`ag`, `ef`, `au`, …) and `p ∼ q`, then
> `evaluate(φ, p) = evaluate(φ, q)`. Consequently a behavioral guard is well-defined
> on the bisimulation quotient `S / ∼` — it is a property of the *process up to
> behavior*, not of its representation. This is the GSLT/MeTTaIL instance of the
> Hennessy–Milner correspondence — the project's stated main behavioral-equivalence
> result ("processes are bisimilar iff they satisfy the same formulae",
> `docs/papers/plan.md`), of which the mechanized `RegisterEquivalence.v` bisimulation
> and the `bisimulation.rs` Heyting-SFA bisimilarity are the building blocks.

### 4.2 Why this lands inside the Heyting frame, not beside it

Bisimulation is not a separate concern bolted onto the intuitionistic story — it *is*
the intuitionistic story read on the model side:

- **Bisimulations are the p-morphisms (bounded morphisms) of Kripke/intuitionistic
  semantics.** Intuitionistic validity is preserved by the very maps that preserve
  bisimulation; a behavioral predicate respecting `∼` is the order-theoretic analog of
  an *open* (observable) property in §2.4. Observability, openness, and
  bisimulation-invariance are three names for one condition.
- **`∼` is a greatest fixed point — the same shape as the behavioral semantics.** The
  safety operator `AG` is `νX. (… ∧ [-]X)` (a greatest fixed point in
  `behavioral_algebra.rs`), and bisimilarity is the greatest bisimulation. Both are
  coinductive: "holds unless finitely refuted." This is why a behavioral predicate's
  indeterminacy (§3) and a process's behavioral identity (`∼`) are computed by the same
  partition-refinement / fixpoint machinery, and why `bisimulation.rs` is literally the
  *Heyting-SFA* bisimilarity layer.
- **Bisimulation-invariance carves the behavioral fragment from the structural one.**
  Structural (Boolean) predicates *may* distinguish bisimilar processes — they are about
  syntax and shape, and `¬¬a = a` for them. Behavioral (Heyting) predicates *must not* —
  they live on `S / ∼`, where `¬¬a ≠ a` reflects the semi-decidability of observing
  behavior. So bisimulation-invariance is exactly the boundary between the regular
  (structural, classical) elements and the genuinely-Heyting (behavioral) ones of §5.

## 5. How Heyting completes Boolean for structural-behavioral types

Structural predicates (`BehavioralPred::AcMatch`) are decided exactly — classical
Boolean, every element regular. Behavioral predicates (`BehavioralAlgebra`) are
semi-decidable — Heyting, `¬¬a ≠ a` in general, well-defined only up to bisimulation
(§4). A real guard is typically *both* ("matches pattern `P` ∧ sender `halts`" —
[05 §5](05-algebra-pyramid-and-decidability.md)); neither fragment alone is the whole
predicate type.

![The structural Boolean leg and behavioral Heyting leg combine into `RejectSafeProduct`](figures/12-mixed-product.svg)

PlantUML source: [figures/12-mixed-product.puml](figures/12-mixed-product.puml).

The completion is `RejectSafeProduct<S, B>` with `S` a classical structural leg
(typically `Classical<A>`-wrapped) and `B` a reject-safe behavioral leg. It is
`RejectSafeAlgebra` **only** — never `BooleanAlgebra` (the `compile_fail` doctest in
`algebra_tower.rs` enforces it). Its pseudo-complement is the **asymmetric De Morgan**

`¬(a ∧ b) = (¬a ∧ ⊤) ∨ (⊤ ∧ ¬b)`

with `¬a` exact (structural) and `¬b` reject-safe (behavioral). The *shape* is forced
by §2.1: the intuitionistic `¬(a ∧ b) = ¬a ∨ ¬b` does not hold, so the complement pads
each leg with `⊤` and disjoins — a sound over-approximation, proven never to fire
falsely by `mixed_negation_soundness` / `mixed_guard_no_false_fire` in
`BehavioralNegation.v`, with the runtime mirror `mixed_negation_soundness` (and
`comm_fires_iff`, `rho_complement_no_commit`) in `RhoGuardedCommSoundness.v`.

### 5.1 In what sense Heyting *completes* Boolean

The relationship is **subsumes-and-extends**: every Boolean algebra *is* a Heyting
algebra (with `a → b = ¬a ∨ b`, every element regular), and the regular elements of any
Heyting algebra form a Boolean algebra (§2.3). So Heyting completes Boolean in the
precise sense that (i) it contains Boolean as the all-regular special case, and (ii) it
adds exactly the structure the non-regular (semi-decidable) elements need, with Boolean
recoverable on the regular sublattice. The code realizes (i) as `Classical<A>`
(`regularize = id`) and (ii) as `BehavioralAlgebra: HeytingAlgebra`.

The formal bridge is the **tier ↔ regularity correspondence** in
`GuardTierCertificate.v`: `tier_regularity_reg` maps the exact tiers (T1/T2) to the
regular Boolean core, `tier_regularity_boundary` maps T3 to the boundary
(`Sat3::DontKnow`) region, and `tier_regularity_closed` maps T4 to the
refutable/trusted class. Combining a Boolean leg with a Heyting leg yields the weaker
(Heyting) guarantee — the join-semilattice homomorphism `tier_max_sound_hom` /
`tier_max_complete_hom`: a product is exactly as classical as its *most* behavioral
component.

## 6. The OSLF affinity

Constructive logic is the natural logic of *resources* and of *provability*, and that
is why the predicate algebra composes with OSLF. Substructural logics (no weakening or
contraction) are the proof theory of resource-sensitive reasoning, whose natural
fragment is intuitionistic; the BHK reading is itself a reading of constructive
provability. Both traditions reject "true because not-false."

The sharpest correspondence — `reject-underfunded ≈ reject-safe`
([09 §3](09-oslf-composition.md)) — now has its *logical* explanation. The reject-safe
pseudo-complement asserts `¬φ` only on refuting evidence; OSLF's `law_reject_underfunded`
refuses a rewrite only when supply provably fails to cover demand
(`is_funded(Δ, Σ, margin) = Δ + margin ≤ Σ`, a decidable total judgment, `law_decidable`
in `MettaOslfLawsConformance.v`). Both are **fail-closed**: never assert or grant on
*absence* of evidence. The unifier is the constructive stance — *assertion requires
construction*. A false grant (firing an unaffordable rewrite, or committing on an
unproven guard) is **unsound**; a false refusal is merely **incomplete**.
Intuitionistic logic is precisely the logic that prefers incompleteness to unsoundness,
which is why it is the right logic for *both* axes.

This explains *why* the two axes of [09](09-oslf-composition.md) compose into a plain
conjunction `guard-satisfied ∧ funded`: both are constructive and fail-closed for the
same reason, each monotone in its "more evidence" order (more facts never retract a
witness; `law_supply_monotone`: more supply never revokes funding), each decidable with
an honest bottom (`Sat3::DontKnow`; the funding judgment is total). A resource logic and
an evidence logic are both constructive logics, so their `∧` is well-behaved. The
honest nuance of [09 §5](09-oslf-composition.md) stands: the predicate algebra is not
OSLF and neither contains the other; the alignment is the shared constructive
discipline, the cleanliness is the separation.

## 7. Worked logical example

Take the invariance guard `safe(P) := AG ¬bad(P) = νX. (¬bad ∧ [-]X)` — the real `ag`
operator of `behavioral_algebra.rs`, with `bad` a state proposition. Evaluation is
greatest-fixpoint model checking over the reachable LTS.

- **Why `¬¬safe(P) ≠ safe(P)` operationally.** A bounded check of `safe(P)` explores
  the reachable LTS up to `MAX_REACH_STATES`. Finding no `bad` within the explored
  region returns true *for that snapshot*, but if the LTS is truncated (or `bad` is
  reachable only beyond the cap) the modal `is_satisfiable_3v(safe(P))` is honestly
  `Sat3::DontKnow`. The double pseudo-complement `¬¬safe(P)` ("`safe(P)` is not
  refuted") is *weaker* than `safe(P)` ("invariance is verified"): a bounded check that
  did not refute safety is not a proof of safety. Algebraically this is the
  `a ≤ ¬¬a` of `dneg_extensive` with the converse unavailable off the regulars;
  operationally it is the gap between "no counterexample found within budget" (`¬¬safe`,
  the boundary / `DontKnow` region) and "invariance established" (`safe`, a regular /
  decidable witness).
- **Why `safe(P) ∨ ¬safe(P)` is not assertible.** To assert the disjunction
  constructively we must assert a disjunct: exhibit a run reaching `bad` (a witness for
  `¬safe`, i.e. `EF bad`) or *prove* no run ever reaches `bad` (`safe`). A bounded model
  check that neither found a `bad`-reaching run nor exhausted the state space yields
  **neither**, and `Sat3` propagates it: `DontKnow ∨ ¬DontKnow = DontKnow`. Contrast the
  *structural* guard `x > 0`, which is decidable and does satisfy excluded middle — the
  recovered-classical, regular case.
- **Bisimulation closes the loop.** If `P ∼ Q` then `safe(P) = safe(Q)` (Theorem 4.2):
  the guard is a property of behavior, so the indeterminacy above is a fact about the
  *behavior* `[P]_∼`, not about how `P` is written.

The payoff: the indeterminacy is not a defect of the checker but the honest logical
content of a semi-decidable, bisimulation-invariant property, and the reject-safe
discipline is what keeps a `DontKnow` from ever firing a COMM
([08](08-runtime-comm-enforcement.md), [05 Theorem 5.1](05-algebra-pyramid-and-decidability.md)).

## 8. The mechanized account

All theories below are zero-admission; build with
`make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-symbolic-algebra` (and
`=rocq-rho-bridge` for the bridge rows). The `Sat3`/`Esakia` caveat of the front-matter
applies: these names are Rust / theory, not Coq.

| Claim (argued in §) | File | Key theorem(s) |
|---|---|---|
| partial order, glb, the Heyting adjunction (§2) | `HeytingAlgebra.v` | `le_refl`, `le_antisym`, `le_trans`, `meet_glb_l`, `meet_glb_r`, `himp_adj` |
| modus ponens / counit (§2) | `HeytingAlgebra.v` | `imp_counit`, `imp_meet` |
| `¬¬` is a closure operator; triple/quad negation (§2.2) | `HeytingAlgebra.v` | `dneg_extensive`, `dneg_mono`, `neg_triple`, `dneg_idempotent` |
| reject-safe soundness `¬¬a = ⊥ ⇒ a = ⊥` (§2.2, §3) | `HeytingAlgebra.v` | `dneg_eq_bot_implies_bot` |
| regular elements Booleanize `H` (§2.3, §5.1) | `HeytingAlgebra.v` | `regular`, `neg_regular`, `regular_bot`, `regular_top`, `regular_meet`, `excluded_middle_reg`, `neg_involutive_on_regular` |
| excluded middle genuinely fails; no classical complement (§3.3) | `BehavioralNegation.v` | `TriModel`: `tri_neg_sound`, `excluded_middle_fails`, `no_classical_complement` |
| asymmetric De Morgan complement is reject-safe (§5) | `BehavioralNegation.v` | `mixed_negation_soundness`, `mixed_guard_no_false_fire`, `weak_dneg` |
| …the runtime / COMM mirror (§5, §6) | `RhoGuardedCommSoundness.v` | `mixed_negation_soundness`, `comm_fires_iff`, `product_eval_sound`, `rho_complement_no_commit`, `rho_guard_true_commits` |
| every classical EBA is reject-safe (§5.1) | `EffectiveBooleanAlgebra.v` | `RejectSafeLaws`, `eba_implies_reject_safe` |
| tier ↔ regularity; combination homomorphism (§5.1) | `GuardTierCertificate.v` | `tier_regularity_reg`, `tier_regularity_boundary`, `tier_regularity_closed`, `tier_max_sound_hom`, `tier_max_complete_hom` |
| bisimulation is reflexive and a fixed point (§4) | `RegisterEquivalence.v` | `bisimilar`, `is_bisimulation`, `self_bisimilar`, `fixed_point_is_bisimulation` |
| OSLF fail-closed funding laws (§6) | `MettaOslfLawsConformance.v` | `law_reject_underfunded`, `law_decidable`, `law_supply_monotone`, `law_sound` |

The Hennessy–Milner correspondence for GSLT/MeTTaIL (Theorem 4.2's "bisimilar iff same
formulas") is the project's stated behavioral-equivalence result
(`docs/papers/plan.md`); `RegisterEquivalence.v`'s mechanized bisimulation and
`bisimulation.rs`'s Heyting-SFA bisimilarity are its computational substrate.

## 9. Cross-references

- The tower this document deepens, and the reject-safe `compile_fail` safety property:
  [05 — Algebra Pyramid and Decidability](05-algebra-pyramid-and-decidability.md).
- The classical EBA that Heyting subsumes:
  [02 — Effective Boolean Algebra](02-effective-boolean-algebra.md).
- The two-axis composition this document argues for:
  [09 — OSLF Composition](09-oslf-composition.md).
- The full proof ledger and the `Sat3`/`Esakia` caveat:
  [10 — Formal Verification and Tests](10-formal-verification-and-tests.md).
- Glossary entries for **Regular element**, `Sat3`, `RejectSafeAlgebra`,
  `HeytingAlgebra`, `Classical<A>`, `RejectSafeProduct`:
  [01 — Concepts and Glossary](01-concepts-and-glossary.md).
- Literature: the Heyting / intuitionistic / topology / duality / bisimulation entries
  in [References](references.md), plus
  [Stay & Meredith, 2016](references.md#stay-meredith-2016) for OSLF.
