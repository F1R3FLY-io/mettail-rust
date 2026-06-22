# Effective Boolean Algebra

Last updated: 2026-06-22

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
denotational equivalence in `EffectiveBooleanAlgebra.v` (`conj_comm`, `disj_comm`,
`conj_assoc`, `absorb_conj_disj`, … — about 28 derived identities, all `Qed`).

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
> this path. This is a deliberate trade documented in
> `prattail/docs/design/constraint-theories/why-automata-instead-of-solvers.md`:
> automata give closure and exactness over the *whole* algebra (complement,
> projection, equivalence), which a solver's per-query yes/no cannot.

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
  to `⊥` (a sort mismatch is *unsatisfiable*, not a type error).
- A `Sort` registry (`Native(NativeKind) | Category | Tuple | Sum | List | Bag |
  Map`) indexes each language type to its algebra; `SortRegistry::from_grammar`
  derives the family from the `language!` `NativeKind`s and grammar categories,
  with **no hard-coded category list** — the boundary contract with the backend.

The closure constructors (`ProductAlgebra`, `SumAlgebra`, `BagAlgebra`,
`MapAlgebra`, `ListAlgebra`, `TreeAlgebra`) and the tower discipline they live in
are covered in [05](05-algebra-pyramid-and-decidability.md); each is itself a
`BooleanAlgebra` (or a reject-safe algebra), so the SFA/SFT code is reused verbatim
and the algebra-agnostic Coq proofs apply unchanged.

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
