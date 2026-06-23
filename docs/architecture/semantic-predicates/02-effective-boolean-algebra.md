# Effective Boolean Algebra

Last updated: 2026-06-23

All symbols are defined in [Concepts and Glossary](01-concepts-and-glossary.md).
This document is the algebraic foundation: what an effective Boolean algebra (EBA)
is, the `BooleanAlgebra` trait that realizes it, the decision procedures it must
provide, why *minterms* make symbolic algorithms finite, and the concrete algebra
instances that populate the family.

## 1. Why predicates instead of symbols

A classical finite automaton labels each transition with a single symbol drawn
from a finite alphabet `Σ`. That is fine for `Σ = {a, b, c}` and hopeless for
`Σ = ℤ` or `Σ = char` or `Σ = {all process terms}`. A **symbolic** automaton
labels each transition with a *predicate* `φ` over a (possibly infinite) domain
`D`, and a transition fires on input `e` when `e ⊨ φ`.

To run the standard automaton algorithms — emptiness, intersection, complement,
determinization, equivalence — over predicates rather than symbols, the predicate
algebra must support a fixed set of *computable* operations. That algebra is an
**effective Boolean algebra** ([D'Antoni & Veanes, 2017](references.md#dantoni-veanes-2017)).

## 2. The formal object

> **Definition 2.1 (Effective Boolean Algebra).** An effective Boolean algebra is
> a tuple `𝓐 = (Φ, D, ⟦·⟧, ⊤, ⊥, ∧, ∨, ¬, sat, witness)` where:
> - `Φ` is a set of *predicates* and `D` a *domain* of elements;
> - `⟦·⟧ : Φ → 𝒫(D)` is the *denotation*, a homomorphism: `⟦⊤⟧ = D`, `⟦⊥⟧ = ∅`,
>   `⟦φ ∧ ψ⟧ = ⟦φ⟧ ∩ ⟦ψ⟧`, `⟦φ ∨ ψ⟧ = ⟦φ⟧ ∪ ⟦ψ⟧`, `⟦¬φ⟧ = D ∖ ⟦φ⟧`;
> - `sat : Φ → 𝔹` *decides* `⟦φ⟧ ≠ ∅`;
> - `witness : Φ → Option D` returns some `e ∈ ⟦φ⟧` when `sat(φ)`.
>
> "Effective" means each of `∧`, `∨`, `¬`, `sat`, `witness`, and the membership
> test `e ⊨ φ` is given by an algorithm.

The Boolean laws hold *up to denotation*: `⟦a ∧ ¬a⟧ = ∅`, `⟦a ∨ ¬a⟧ = D`,
commutativity, associativity, idempotence, absorption, and De Morgan all hold as
set identities. The mechanized version proves these as a setoid quotient by
denotational equivalence (about 28 derived identities, all `Qed`); the load-bearing
ones are stated and proved next.

### 2.1 The classical Boolean laws (the proof-home)

This is the proof-home for the effective-Boolean-algebra laws: each law the rest of
the suite cites is stated here as a Lemma or Proposition and proved in prose, with the
mechanizing Coq name given only as a parenthetical citation. The carrier is the
mechanized record `EBA` of `EffectiveBooleanAlgebra.v`: a domain `D`, a predicate
syntax `Φ`, the constructors `⊤, ⊥, ∧, ∨, ¬`, and three decision procedures
`eval : Φ → D → 𝔹`, `sat : Φ → 𝔹`, `wit : Φ → Option D`. Two predicates are
**denotationally equivalent**, written `p ≈ q`, when they evaluate alike everywhere:

`p ≈ q  :⟺  ∀d. eval p d = eval q d`

(mechanized as `equiv`, with notation `p ≈[A] q`). All Boolean identities below are
stated up to `≈`, because the Rust `and`/`or`/`not` are *syntactic* constructors that
are lawful only up to denotation. The proofs are uniform: unfold each side through the
homomorphism contract of Proposition 2.2, then decide the resulting Boolean expression
by truth table on the finitely-many values of `eval _ d`.

**Proposition 2.2 (the EBA contract — `eval` is a Boolean homomorphism; `sat`/`wit`
are sound and complete).** An EBA satisfies the laws `EBA_Laws`:

- **homomorphism:** `eval ⊤ d = true`, `eval ⊥ d = false`,
  `eval (p ∧ q) d = eval p d && eval q d`, `eval (p ∨ q) d = eval p d || eval q d`, and
  `eval (¬p) d = negb (eval p d)`;
- **`sat` sound and complete:** `sat p = true ⟹ ∃d. eval p d = true`, and conversely
  `eval p d = true ⟹ sat p = true`;
- **`wit` sound and total:** `wit p = Some d ⟹ eval p d = true`, and
  `sat p = true ⟹ ∃d. wit p = Some d`.

*Proof.* This is the contract that *defines* an effective Boolean algebra rather than a
theorem derived within one — it is the record `EBA_Laws` whose fields are exactly the
five homomorphism equations (`eval_top`, `eval_bot`, `eval_conj`, `eval_disj`,
`eval_neg`), the two satisfiability equations (`sat_sound`, `sat_complete`), and the two
witness equations (`wit_sound`, `wit_total`). Each shipped instance discharges these
fields when it is constructed; every law below is then derived from them. The contract
is consistent because it is inhabited — for instance by the two-element algebra
`D = unit`, `Φ = 𝔹`, `eval b _ = b`, `sat = id`, `wit true = Some tt`,
`wit false = None` — so assuming it introduces no contradiction. `∎`
(The record is `EBA_Laws` in `EffectiveBooleanAlgebra.v`, fields
`eval_top`/`eval_bot`/`eval_conj`/`eval_disj`/`eval_neg`, `sat_sound`/`sat_complete`,
`wit_sound`/`wit_total`.)

**Lemma 2.3 (excluded middle).** `p ∨ ¬p ≈ ⊤`.

*Proof.* Fix `d`. By the homomorphism (Proposition 2.2),
`eval (p ∨ ¬p) d = eval p d || negb (eval p d)` and `eval ⊤ d = true`. Decide on the
value of `eval p d`: if `true`, then `true || negb true = true || false = true`; if
`false`, then `false || negb false = false || true = true`. In both cases the left side
equals `true = eval ⊤ d`, so `p ∨ ¬p ≈ ⊤`. `∎` (Mechanized as `excluded_middle`.)

**Lemma 2.4 (non-contradiction).** `p ∧ ¬p ≈ ⊥`.

*Proof.* Fix `d`. By Proposition 2.2,
`eval (p ∧ ¬p) d = eval p d && negb (eval p d)` and `eval ⊥ d = false`. If
`eval p d = true`, then `true && negb true = true && false = false`; if `false`, then
`false && negb false = false && true = false`. Either way the left side is
`false = eval ⊥ d`, so `p ∧ ¬p ≈ ⊥`. `∎` (Mechanized as `non_contradiction`.)

**Lemma 2.5 (double negation).** `¬¬p ≈ p`.

*Proof.* Fix `d`. Applying the negation clause of Proposition 2.2 twice,
`eval (¬¬p) d = negb (negb (eval p d))`. The Boolean `negb` is an involution
(`negb (negb b) = b`, by cases `b = true` and `b = false`), so
`eval (¬¬p) d = eval p d`. Hence `¬¬p ≈ p`. `∎` (Mechanized as `double_neg`, using
`negb_involutive`.) This is the law that makes `¬` **involutive** — the defining mark
of the *classical* tier; the behavioral tier keeps only the one-directional
`p ≤ ¬¬p` ([12 Lemma 2.6](12-heyting-behavioral-logic.md)).

**Lemma 2.6 (De Morgan, conjunction).** `¬(p ∧ q) ≈ ¬p ∨ ¬q`.

*Proof.* Fix `d`. Through Proposition 2.2 the left side is
`negb (eval p d && eval q d)` and the right side is `negb (eval p d) || negb (eval q d)`.
These coincide by the four-row Boolean truth table for `negb (a && b) = negb a || negb b`:

| `eval p d` | `eval q d` | `negb(a && b)` | `negb a \|\| negb b` |
|---|---|---|---|
| `true`  | `true`  | `negb true = false`  | `false \|\| false = false` |
| `true`  | `false` | `negb false = true`  | `false \|\| true  = true`  |
| `false` | `true`  | `negb false = true`  | `true  \|\| false = true`  |
| `false` | `false` | `negb false = true`  | `true  \|\| true  = true`  |

Every row agrees, so `¬(p ∧ q) ≈ ¬p ∨ ¬q`. `∎` (Mechanized as `de_morgan_conj`; its
dual `¬(p ∨ q) ≈ ¬p ∧ ¬q` is `de_morgan_disj`.) Unlike the Heyting tier, **both**
directions and **both** De Morgan duals hold classically, because `¬` is involutive
(Lemma 2.5); the behavioral tier loses the `¬(p ∧ q)` direction
([12 §2.1](12-heyting-behavioral-logic.md)).

The remaining identities mentioned above — commutativity `conj_comm`/`disj_comm`,
associativity `conj_assoc`/`disj_assoc`, idempotence `conj_idem`/`disj_idem`,
absorption `absorb_conj_disj`/`absorb_disj_conj`, distributivity
`distrib_conj_disj`/`distrib_disj_conj`, and the unit/annihilator laws
`conj_top`/`disj_bot`/`conj_bot`/`disj_top` — are proved the same way (unfold through
Proposition 2.2, then truth-table) and are collected with their Coq names in §8. The
four derived analysis operators are then satisfiability queries over these laws:
`implies` is `decides_implies p q := negb (sat (p ∧ ¬q))` (correct by `implies_correct`),
`is_tautology` is `decides_tautology p := negb (sat (¬p))` (`tautology_correct`),
`overlaps` is `decides_overlaps p q := sat (p ∧ q)` (`overlaps_correct`), and
`equivalent` is their conjunction (`equivalent_correct`) — the bridge §3 draws from
algebra to analysis.

**Proposition 2.7 (every classical EBA is reject-safe).** Every EBA satisfying
`EBA_Laws` also satisfies the weaker **reject-safe** contract `RejectSafeLaws`: it keeps
the `∧`/`∨` homomorphism and the `sat`/`wit` soundness laws, and in place of the
classical involutive negation it has only the one-directional **reject-safe negation**
`eval (¬p) d = true ⟹ eval p d = false`. Thus the classical tier sits at the base of the
tower `BooleanAlgebra : HeytingAlgebra : RejectSafeAlgebra`, and every decidable algebra
drops into the reject-safe-bounded SFA/SFT machinery with no obligation of its own.

*Proof.* The conjunction/disjunction homomorphism and the `sat`/`wit` soundness laws are
shared verbatim between the two contracts. For reject-safe negation, assume
`eval (¬p) d = true`; by the classical negation clause (Proposition 2.2)
`eval (¬p) d = negb (eval p d)`, so `negb (eval p d) = true`, whence `eval p d = false`.
This is the substance; the full statement is the cross-referenced tower result. `∎`
This proposition is **proved in doc 12**: see
[12 — Proposition 6.2 (every classical EBA is reject-safe)](12-heyting-behavioral-logic.md);
it is mechanized as `eba_implies_reject_safe` (from the record `RejectSafeLaws`) in
`EffectiveBooleanAlgebra.v`. It is restated here, and not re-proved, because doc 12 is
the home of the reject-safe / Heyting tower, while this document is the home of the
classical laws it generalizes.

## 3. The trait

The Rust realization is `prattail/src/symbolic.rs::BooleanAlgebra`. It is the
single interface every automaton algorithm is written against:

```rust
pub trait BooleanAlgebra {
    type Predicate: Clone + Eq + Hash;
    type Domain;

    // constructors
    fn true_pred(&self) -> Self::Predicate;            // ⊤
    fn false_pred(&self) -> Self::Predicate;           // ⊥
    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;  // ∧
    fn or(&self,  a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;  // ∨
    fn not(&self, a: &Self::Predicate) -> Self::Predicate;                       // ¬ (involutive)

    // decisions
    fn is_satisfiable(&self, a: &Self::Predicate) -> bool;                       // sat
    fn witness(&self, a: &Self::Predicate) -> Option<Self::Domain>;
    fn evaluate(&self, a: &Self::Predicate, e: &Self::Domain) -> bool;           // e ⊨ φ

    // derived (default methods)
    fn implies(&self, a, b) -> bool { !self.is_satisfiable(&self.and(a, &self.not(b))) }
    fn equivalent(&self, a, b) -> bool { self.implies(a, b) && self.implies(b, a) }
    fn is_tautology(&self, a) -> bool { !self.is_satisfiable(&self.not(a)) }
    fn overlaps(&self, a, b) -> bool { self.is_satisfiable(&self.and(a, b)) }
}
```

The derived methods are the bridge from algebra to *analysis*: `implies` is
language inclusion of one guard in another, `overlaps` is dispatch ambiguity, and
`is_tautology` is "this guard always fires." Every one reduces to `is_satisfiable`,
which is why **satisfiability is the single decision procedure each instance must
get right**.

This trait is the *classical* tier — `not` is involutive (`¬¬a = a`) and
`is_satisfiable` is two-valued. The semi-decidable behavioral algebras live one
tier weaker and are introduced in
[05 — Algebra Pyramid and Decidability](05-algebra-pyramid-and-decidability.md);
everything in *this* document is classical.

## 4. Minterms: making the symbolic alphabet finite

Determinization and equivalence need to reason about "all the ways the guards on a
state's outgoing edges can be jointly satisfied." Enumerating `D` is impossible;
enumerating the **minterms** is not.

> **Definition 4.1 (Minterm).** Given a finite predicate set `Ψ = {φ₁, …, φₖ}`, a
> *minterm* is a satisfiable conjunction `ψ̃₁ ∧ … ∧ ψ̃ₖ` where each `ψ̃ᵢ` is either
> `φᵢ` or `¬φᵢ`. The set of minterms `Minterms(Ψ)` partitions `D`: every element
> falls in exactly one minterm, and within a minterm every element is treated
> identically by every guard in `Ψ`.

Minterms are the finite effective alphabet. The number of minterms is at most
`2ᵏ` but usually far fewer, because most sign combinations are unsatisfiable and
are pruned by `sat`. The construction is literate below.

> **Algorithm `Minterms` — partition the domain by a guard set.**
> *Input:* an EBA `𝓐` and a predicate set `Ψ = {φ₁, …, φₖ}`.
> *Output:* the satisfiable minterms partitioning `D`.
>
> ```
> Minterms(𝓐, Ψ):
>   frontier ← { ⊤ }                       ▷ start with the whole domain
>   for φ in Ψ:                            ▷ refine by one guard at a time
>     next ← ∅
>     for m in frontier:
>       for sign in { φ, ¬φ }:
>         c ← 𝓐.and(m, sign)
>         if 𝓐.is_satisfiable(c):          ▷ drop empty cells eagerly
>           next ← next ∪ { c }
>     frontier ← next
>   return frontier
> ```
>
> Each refinement at most doubles the cell count, and `is_satisfiable` prunes
> every empty cell immediately, so the live frontier stays small whenever the
> guards are mostly disjoint. The Rust entry point is `compute_minterms`
> (`symbolic.rs`).

With minterms in hand, determinization is classical subset construction over the
minterm alphabet, and equivalence is a product emptiness check — both detailed in
[03 — Symbolic Automata (SFA)](03-symbolic-automata-sfa.md).

## 5. The concrete instances

Generalizing the framework "over all data types" is *populating the family of
EBA instances*, because every algorithm is already written against the trait. The
shipped instances:

| Instance | Domain `D` | Predicate shape | File |
|---|---|---|---|
| `IntervalAlgebra` | `i64` | unions of half-open ranges `[lo, hi)` | `symbolic.rs` |
| `CharClassAlgebra` | `char` | unions of Unicode ranges | `symbolic.rs` |
| `KatBooleanAlgebra` | propositional worlds | KAT `BooleanTest` formulas | `symbolic.rs` |
| `PresburgerAlgebra` | `ℤⁿ` | linear-integer-arithmetic formulas, decided by a binary-encoded NFA | `presburger.rs` |
| `StringAlgebra` | `String` | regular languages, as an SFA over `char` | `string_algebra.rs` / `regex_sfa.rs` |
| `OrderedFieldAlgebra<P>` | `BigInt`/`BigRat`/`Fixed`/`Float` | interval unions with `±∞` endpoints, density-aware witnesses | `ordered_field.rs` |
| `ProductAlgebra<A,B>` | `D_A × D_B` | classical cartesian-product predicates | `symbolic.rs` |
| `BagAlgebra<A>` / `MapAlgebra<K,V>` / `ListAlgebra<A>` | multisets / maps / sequences | per-minterm count vectors / key×value / SFA | `collection_algebra.rs` |
| `TreeAlgebra<A>` | ranked trees | "constructor `c` ∧ payload ⊨ φ ∧ childᵢ ⊨ φᵢ" | `sym_tree.rs` |
| `AnyAlgebra` | any of the above | a closed-enum uniform carrier | `any_algebra.rs` |

> **Note on satisfiability — automata, not SMT.** The integer instances decide
> satisfiability *automata-theoretically*, not via an external SMT solver. A
> Presburger predicate is compiled to a remainder NFA over the binary encoding of
> its integers ([Büchi, 1960](references.md#buchi-1960);
> [Bartzis & Bultan, 2003](references.md#bartzis-bultan-2003)); `is_satisfiable`
> is NFA non-emptiness (`is_satisfiable_nfa`, `presburger.rs`). There is no Z3 in
> this path. (The substrate *does* ship a Z3/SMT backend, but only as a
> `Sat3`-only secondary gap-filler for the mixed bit-vector guards the automata
> cannot express — [13 §2.1](13-constraint-theory-engine.md); it is never the
> integer decision procedure here.) This is a deliberate trade documented in
> `prattail/docs/design/constraint-theories/why-automata-instead-of-solvers.md`:
> automata give closure and exactness over the *whole* algebra (complement,
> projection, equivalence), which a solver's per-query yes/no cannot.

### 5.1 The Presburger instance, proved (no SMT solver)

This is the proof-home for the **Presburger instance**, the canonical witness that an
EBA need not call out to a solver. A Presburger-definable set is a decidable subset of
`ℤ`, so the mechanized model in `PresburgerBooleanAlgebra.v` takes the predicate type
to be Boolean-valued functions and the equivalence to be pointwise equality:

`Pred := ℤ → bool`,  `P ≈ Q  :⟺  ∀z. P z = Q z`

(mechanized as `Pred` and `pred_eq`). The Boolean-valued reading *is* decidability:
`P z` is precisely NFA acceptance of the binary encoding of `z`
([Büchi, 1960](references.md#buchi-1960)), and the three Boolean constructors are the
three NFA constructions —

| Boolean op | Definition (`P, Q : Pred`) | NFA construction (`presburger.rs`) |
|---|---|---|
| `P ∧ Q` (`pred_and`) | `fun z ⟼ P z && Q z` | product / intersection (`intersect_nfa`) |
| `P ∨ Q` (`pred_or`) | `fun z ⟼ P z \|\| Q z` | product / union (`union_nfa`) |
| `¬P` (`pred_not`) | `fun z ⟼ negb (P z)` | determinize + complement (`complement_nfa`) |

with `⊤ := fun _ ⟼ true` (`pred_true`, universal acceptance) and
`⊥ := fun _ ⟼ false` (`pred_false`, empty NFA). Satisfiability is NFA non-emptiness
(`is_satisfiable_nfa`), so no Z3 ever appears *in the Presburger path* (the optional
Z3/SMT backend of [13 §2.1](13-constraint-theory-engine.md) is a separate, `Sat3`-only
gap-filler). The first obligation is that each NFA op
**coincides definitionally** with its Boolean op.

**Lemma 5.1 (NFA Boolean ops are the Boolean ops).** For all `P, Q : Pred` and `z : ℤ`,

`(P ∧ Q) z = P z && Q z`,  `(P ∨ Q) z = P z || Q z`,  `(¬P) z = negb (P z)`.

*Proof.* Each holds by unfolding the corresponding definition: `pred_and P Q z` is
`P z && Q z` by the definition of `pred_and`, and likewise `pred_or P Q z` is
`P z || Q z` and `pred_not P z` is `negb (P z)`, each immediately by `reflexivity`. So
the product NFA's acceptance is exactly `&&`, the union NFA's is exactly `||`, and the
complement NFA's is exactly `negb`. `∎` (Mechanized as `nfa_intersect_correct`,
`nfa_union_correct`, `nfa_complement_correct`.)

Because the ops are literally `&&`, `||`, `negb` on `ℤ → bool`, the Boolean-algebra laws
reduce — as in §2.1 — to truth tables on the finitely many values of `P z, Q z, R z`.

**Lemma 5.2 (complement annihilation and excluded middle).**
`P ∧ ¬P ≈ ⊥` and `P ∨ ¬P ≈ ⊤`.

*Proof.* Fix `z` and decide on `P z`. For annihilation,
`(P ∧ ¬P) z = P z && negb (P z)`, which is `true && false = false` when `P z = true` and
`false && true = false` when `P z = false`; either way it equals `⊥ z = false`. For
excluded middle, `(P ∨ ¬P) z = P z || negb (P z)`, which is `true || false = true` when
`P z = true` and `false || true = true` when `P z = false`; either way it equals
`⊤ z = true`. `∎` (Mechanized as `complement_and` and `complement_or`. The NFA reading:
intersecting an automaton with its complement gives the empty automaton, and their
union gives the universal automaton.)

**Lemma 5.3 (De Morgan).** `¬(P ∧ Q) ≈ ¬P ∨ ¬Q` and `¬(P ∨ Q) ≈ ¬P ∧ ¬Q`.

*Proof.* Fix `z`. For the first, `(¬(P ∧ Q)) z = negb (P z && Q z)` and
`(¬P ∨ ¬Q) z = negb (P z) || negb (Q z)`, equal by the four-row truth table for
`negb (a && b) = negb a || negb b` (the table of Lemma 2.6, with `a := P z`, `b := Q z`).
For the second, `(¬(P ∨ Q)) z = negb (P z || Q z)` and
`(¬P ∧ ¬Q) z = negb (P z) && negb (Q z)`, equal by the dual table
`negb (a || b) = negb a && negb b`. Both directions of both duals hold because `negb` is
classical here. `∎` (Mechanized as `de_morgan_and` and `de_morgan_or`.)

**Lemma 5.4 (distributivity).**
`P ∧ (Q ∨ R) ≈ (P ∧ Q) ∨ (P ∧ R)` and `P ∨ (Q ∧ R) ≈ (P ∨ Q) ∧ (P ∨ R)`.

*Proof.* Fix `z`. Each side unfolds (Lemma 5.1) to a Boolean expression over the three
values `P z, Q z, R z`; exhausting the `2³ = 8` assignments shows the two sides agree in
every row. For instance with `P z = true` the meet-over-join law reduces to
`true && (Q z || R z) = (true && Q z) || (true && R z)`, i.e. `Q z || R z` on both sides;
with `P z = false` both sides are `false`. The join-over-meet law is the dual
enumeration. `∎` (Mechanized as `distributivity_and_or` and `distributivity_or_and`.)

The remaining Presburger laws — commutativity `and_comm`/`or_comm`, associativity
`and_assoc`/`or_assoc`, absorption `absorption_and_or`/`absorption_or_and`,
idempotence `and_idempotent`/`or_idempotent`, the unit/annihilator laws
`and_true`/`or_false`/`and_false`/`or_true`, and double negation `double_negation`
(`¬¬P ≈ P`, by involution of `negb`) — close the Boolean algebra and are proved by the
identical truth-table method; their Coq names are collected in §8. Together they
establish that the NFA-defined Presburger predicates form a Boolean algebra **purely
automata-theoretically**, which is what lets `complement`, projection, and equivalence
be exact over the whole algebra rather than a per-query solver verdict.

## 6. The uniform carrier `AnyAlgebra`

`prattail/src/any_algebra.rs` provides a single **closed-enum** carrier so that
one concrete `Predicate`/`Domain` pair drops directly into the SFA/SFT/tree
machinery by `match` dispatch — with **no `dyn`** (which would break the `Eq +
Hash` bounds the automata require and inject allocation into the hot path), and it
is the only design that lets a tree node's heterogeneous children share one
algebra.

- `AnyDomain` carries 8 scalar leaves (`Int`, `Char`, `Bool`, `BigInt`, `BigRat`,
  `Fixed`, `Float`, `Str`) plus 6 combinator variants (`Product`, `Sum`, `List`,
  `Bag`, `Map`, `Tree`); the `Sum` and `Tree` payloads are boxed to keep the enum
  finitely sized.
- `AnyPred` / `AnyAlgebra` mirror the domain. `fold_pred` is the many-sorted
  projection: a predicate of sort `Int` evaluated against a `Bool` element folds
  to `⊥` (a sort mismatch is *unsatisfiable*, not a type error). This projection is
  mechanized zero-admission as `fold_all_foreign_unsat` (foreign sort `⊥`) and
  `wrapper_eval_faithful` / `wrapper_sat_faithful` (the wrapper agrees with the bare
  leaf) in `AnyAlgebraProjectionSound.v`
  ([10 §2.1](10-formal-verification-and-tests.md)).
- A `Sort` registry (`Native(NativeKind) | Category | Tuple | Sum | List | Bag |
  Map`) indexes each language type to its algebra; `SortRegistry::from_grammar`
  derives the family from the `language!` `NativeKind`s and grammar categories,
  with **no hard-coded category list** — the boundary contract with the backend.

The closure constructors (`ProductAlgebra`, `SumAlgebra`, `BagAlgebra`,
`MapAlgebra`, `ListAlgebra`, `TreeAlgebra`) and the tower discipline they live in
are covered in [05](05-algebra-pyramid-and-decidability.md); each is itself a
`BooleanAlgebra` (or a reject-safe algebra), so the SFA/SFT code is reused verbatim
and the algebra-agnostic Coq proofs apply unchanged.

The carrier is wired into the live guard pipeline behind the `any-algebra-carrier`
Cargo feature, **off by default** (the default build is byte-identical), so the
uniform projection *augments* the per-leaf analyses rather than replacing them.

## 7. What this buys the rest of the suite

Because the EBA fixes a *small, computable* interface and the family is *closed*
under the type constructors, three things follow that the later documents rely on:

1. **One automaton library, every data type.** [03](03-symbolic-automata-sfa.md)
   and [04](04-symbolic-transducers-sft-stft.md) describe the algorithms once;
   they run over integers, characters, processes, bags, and trees unchanged.
2. **Analysis is satisfiability.** Guard overlap, subsumption, dead-guard, and
   ambiguity lints are all `is_satisfiable` queries — see the dispatch and
   disambiguation use in [07](07-language-to-rholang-integration.md).
3. **The classical/semi-decidable split is a type, not a convention.** Only the
   classical tier offers an involutive `not`; the behavioral algebras cannot, and
   the tower in [05](05-algebra-pyramid-and-decidability.md) enforces that at
   compile time.

## 8. The mechanized account

Every result stated above is collected here against its Coq witness, including the
laws cited but not individually re-proved (those proved by the same truth-table method
as their named siblings). All theories are zero-admission; build the EBA tier with
`make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-symbolic-algebra` and the
Presburger tier with `=rocq-presburger`. Both files end with `Print Assumptions` /
`All proofs are COMPLETE` sentinels.

| Result (here) | Coq witness | File |
|---|---|---|
| Definition of `≈` (denotational equivalence) | `equiv` (notation `≈[A]`) | `EffectiveBooleanAlgebra.v` |
| Proposition 2.2 (the EBA contract / Boolean homomorphism, `sat`/`wit` sound+complete) | record `EBA_Laws`: `eval_top`, `eval_bot`, `eval_conj`, `eval_disj`, `eval_neg`, `sat_sound`, `sat_complete`, `wit_sound`, `wit_total` | `EffectiveBooleanAlgebra.v` |
| Lemma 2.3 (excluded middle) | `excluded_middle` | `EffectiveBooleanAlgebra.v` |
| Lemma 2.4 (non-contradiction) | `non_contradiction` | `EffectiveBooleanAlgebra.v` |
| Lemma 2.5 (double negation) | `double_neg` (via `negb_involutive`) | `EffectiveBooleanAlgebra.v` |
| Lemma 2.6 (De Morgan, conjunction) and its dual | `de_morgan_conj`, `de_morgan_disj` | `EffectiveBooleanAlgebra.v` |
| Remaining EBA identities (commutativity, associativity, idempotence, absorption, distributivity, units/annihilators) | `conj_comm`, `disj_comm`, `conj_assoc`, `disj_assoc`, `conj_idem`, `disj_idem`, `absorb_conj_disj`, `absorb_disj_conj`, `distrib_conj_disj`, `distrib_disj_conj`, `conj_top`, `disj_bot`, `conj_bot`, `disj_top` | `EffectiveBooleanAlgebra.v` |
| Derived analysis operators (`implies`/`is_tautology`/`overlaps`/`equivalent`) | `decides_implies`/`implies_correct`, `decides_tautology`/`tautology_correct`, `decides_overlaps`/`overlaps_correct`, `decides_equivalent`/`equivalent_correct`; helpers `sat_false_iff_empty`, `sat_true_iff_inhabited` | `EffectiveBooleanAlgebra.v` |
| Proposition 2.7 (every classical EBA is reject-safe) — *proved in [12 Prop 6.2](12-heyting-behavioral-logic.md)* | record `RejectSafeLaws`; `eba_implies_reject_safe` (and `wit_none_of_unsat`) | `EffectiveBooleanAlgebra.v` |
| Presburger model (`Pred := ℤ → bool`, `pred_eq`) and ops | `Pred`, `pred_eq`, `pred_and`, `pred_or`, `pred_not`, `pred_true`, `pred_false` | `PresburgerBooleanAlgebra.v` |
| Lemma 5.1 (NFA ops are the Boolean ops) | `nfa_intersect_correct`, `nfa_union_correct`, `nfa_complement_correct` | `PresburgerBooleanAlgebra.v` |
| Lemma 5.2 (complement annihilation, excluded middle) | `complement_and`, `complement_or` | `PresburgerBooleanAlgebra.v` |
| Lemma 5.3 (De Morgan) | `de_morgan_and`, `de_morgan_or` | `PresburgerBooleanAlgebra.v` |
| Lemma 5.4 (distributivity) | `distributivity_and_or`, `distributivity_or_and` | `PresburgerBooleanAlgebra.v` |
| Remaining Presburger laws (commutativity, associativity, absorption, idempotence, units/annihilators, double negation) | `and_comm`, `or_comm`, `and_assoc`, `or_assoc`, `absorption_and_or`, `absorption_or_and`, `and_idempotent`, `or_idempotent`, `and_true`, `or_false`, `and_false`, `or_true`, `double_negation` | `PresburgerBooleanAlgebra.v` |
| The `AnyAlgebra` uniform-carrier projection (foreign sort `⊥` unsatisfiable, wrapper faithful, product/sum layers EBA) | `fold_all_foreign_unsat`, `wrapper_eval_faithful`, `wrapper_sat_faithful`, `carrier_product_layer_is_eba`, `carrier_sum_layer_is_eba` | `AnyAlgebraProjectionSound.v` |

The minterm construction (Definition 4.1 and the `Minterms` algorithm of §4) is **not**
a Coq theorem but an algorithm; its implementation is `compute_minterms`
(`prattail/src/symbolic.rs`), and its correctness obligation — that the live cells
partition `D` — is the partition property stated in Definition 4.1, used by the
determinization and equivalence procedures of [03](03-symbolic-automata-sfa.md).
