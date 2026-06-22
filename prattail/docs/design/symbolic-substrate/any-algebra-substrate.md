# The AnyAlgebra Substrate — generalizing symbolic predicates over all data types

> For the end-to-end architecture of how this substrate classifies guards at compile time and how the surviving guard is enforced at run time, see the authoritative suite [`docs/architecture/symbolic-predicates/`](../../../../docs/architecture/symbolic-predicates/README.md).

**Status:** IMPLEMENTED (2026-06-15). This document records the design of the
symbolic-predicate generalization so it can be reconstructed from scratch. Every
component below is live Rust with a zero-admission Rocq proof; the
concept→code→proof map is the table in §7.

---

## 1. Goal and the unifying mechanism

The repo carries the D'Antoni–Veanes substrate for **symbolic finite
automata/transducers** (SFA/SFT): automata whose transitions are guarded by
predicates of an **effective Boolean algebra (EBA)** rather than concrete
symbols (`prattail/src/symbolic.rs` `trait BooleanAlgebra`; `sft.rs`
`SymbolicFiniteTransducer<A,B>`). Because every automaton algorithm
(intersection, complement, determinization, composition, pre/post-image,
functionality) is written **once** against the abstract `BooleanAlgebra` trait,
"generalizing over all supported data types" is **not** a rewrite of the
automata — it is *completing the family of algebra instances and closing it under
the type constructors*, plus adding the tree (structural) and modal (behavioral)
views.

The unifying mechanism: **everything becomes an algebra instance**, the family is
**closed under a small set of combinators**, and downstream SFA/SFT code plus the
algebra-agnostic Coq proofs are reused verbatim.

```
scalar leaves ── combinators ──▶ AnyAlgebra (one carrier)
   Int/Bool/…      Product/Sum/List/Bag/Map/Tree
                                     │
            ┌────────────────────────┼────────────────────────┐
        structural                behavioral               formal
     (tree automata/             (modal/temporal,         (EBA closure +
      transducers)                reject-safe)             tower proofs)
```

## 2. The carrier: `AnyAlgebra` / `AnyPred` / `AnyDomain`

`prattail/src/any_algebra.rs` defines a single **closed-enum** carrier so that
one concrete `Predicate`/`Domain` (each `Eq + Hash + Send + Sync + 'static`)
drops directly into `SymbolicAutomaton`/`SFT`/tree machinery via `match`
dispatch — **no `dyn`** (which would break `Eq + Hash` and inject allocation in
the hot path), and it is the only option letting a tree node's heterogeneous
children share one algebra.

- `AnyDomain`: 8 scalar leaves (`Int/Char/Bool/BigInt/BigRat/Fixed/Float/Str`) +
  6 combinator variants (`Product/Sum/List/Bag/Map/Tree`). `Sum`/`Tree` payloads
  are **boxed** to keep the type finite (a recursive enum storing itself inline
  is infinitely sized).
- `AnyPred` / `AnyAlgebra` mirror the domain; `fold_pred` is the many-sorted
  projection — a foreign-sort leaf folds to ⊥ (a predicate of sort `Int`
  evaluated against a `Bool` domain element is unsatisfiable, not a type error).
- A `Sort` registry (`Native(NativeKind) | Category(String) | Tuple/Sum/List/Bag/
  Map`) indexes each type to its algebra; `SortRegistry::from_grammar(...)`
  derives the family from `NativeKind` + grammar categories (no hard-coded
  category list — boundary contract with the Dovetail/Rho backend).

`impl Singleton for AnyAlgebra` lets the carrier be used as a `MapAlgebra` key
algebra (the key-uniqueness machinery).

## 3. Leaf algebras (per `NativeKind`)

Minted via the existing `TheoryAlgebra<T: ConstraintTheory>` bridge where
possible (the cheap leaf template), else purpose-built:

| Leaf | Algebra | File |
|---|---|---|
| Int | `IntervalAlgebra` / Presburger | `symbolic.rs` / `presburger.rs` |
| Bool | `KatBooleanAlgebra` | `symbolic.rs` |
| Char | `CharClassAlgebra` | `symbolic.rs` |
| Str | `StringAlgebra` = `RegexAlgebra<CharClassAlgebra>` | `string_algebra.rs` / `regex_sfa.rs` |
| BigInt / BigRat / Fixed / i128 | `OrderedFieldAlgebra<P>` (unbounded interval unions, ±∞ endpoints, density-aware witness) | `ordered_field.rs` |
| Float | `OrderedFieldAlgebra<OrderedF64>` (NaN as a point) | `ordered_field.rs` |

`OrderedFieldAlgebra<P>` is generic over an `OrderedPoint` trait (`witness_in`),
with prattail-native `num-bigint`/`num-rational` point types — prattail cannot
depend on `runtime` (cycle), so the points are self-contained.

## 4. Combinators closing the family

The family is closed under (each is itself a `BooleanAlgebra` / reject-safe
algebra, so SFA/SFT code is reused unchanged):

- **N-ary product** `NaryProductAlgebra<A>` (tuples/records) and **sum**
  `SumAlgebra<A>`/`SumPred<P>` (variants/grammar alternation) — `product_nary.rs`.
  Predicates are parameterized by the inner pred type to avoid derive bounds.
- **Collections** — `BagAlgebra<A>` (multisets; minterm-count feasibility),
  `MapAlgebra<K: Singleton, V>` (key×value count + distinct-key cap),
  `ListAlgebra<A>` = `RegexAlgebra<A>` (ordered, via the SFA) —
  `collection_algebra.rs` / `regex_sfa.rs`.
- **Recursive tree** `TreeAlgebra<A>` = symbolic tree automaton (predicate =
  "constructor `c` ∧ payload ⊨ φ ∧ child_i ⊨ φ_i", closed under ∧/∨/¬ by tree-
  automaton product/union/complement) — `sym_tree.rs`. See
  [symbolic-tree-transducer.md](symbolic-tree-transducer.md).

The complement of a collection/tree predicate uses SFA **minterms** (the maximal
satisfiable conjunctions of the element/payload predicates and their negations);
every element falls in exactly one minterm, so a collection is characterized by
its per-minterm count vector (`collection_algebra::minterms`).

**Pattern matching is subsumed.** A first-order pattern → `TreePred<AnyAlgebra>`
(constructor node + `Var` wildcards + symbolic payload guards), with
`match P t ⟺ TreeAlgebra.evaluate(to_treepred(P), to_symterm(t))`. Inhabited ⟺
`is_satisfiable`; `witness` yields a sample matched term the bespoke matcher
cannot produce. Runtime codegen is unchanged; only the compile-time *analysis*
(disjointness/subsumption/dead-guard lints) re-targets onto `TreeAlgebra`.

## 5. The algebra tower (behavioral safety)

Structural predicates are decided exactly (classical `BooleanAlgebra`).
Behavioral predicates (reachability, modal/temporal) are only **semi-decidable**:
their complement is unsound to treat classically. The tower
(`algebra_tower.rs`) makes this a compile-time guarantee:

```
RejectSafeAlgebra   (weakest: and/or/pseudo_complement, is_satisfiable_3v→Sat3;
   ▲                 laws = SAT-soundness + ¬¬-soundness; NO excluded middle)
   │
HeytingAlgebra      (adds implies = the right adjoint of ∧, regularize = ¬¬)
   ▲
BooleanAlgebra      (classical: involutive complement, 2-valued SAT — unchanged)
```

- A classical algebra is lifted via `Classical<A>` (delegates: `pseudo_complement
  = not`, `regularize = id`, `is_satisfiable_3v` only ever `Sat`/`Unsat`).
- A genuinely semi-decidable algebra implements `HeytingAlgebra` **directly and
  does NOT implement `BooleanAlgebra`** — so every operation bounded on
  `BooleanAlgebra` (SFA complement/determinize/exact equivalence) is *statically
  unavailable* on it. That is the load-bearing safety property, verified by the
  `compile_fail` doctest on `RejectSafeProduct`.
- The **mixed guard** `RejectSafeProduct<S, B>` (structural × behavioral) is
  itself `RejectSafeAlgebra` only; its `pseudo_complement` is the asymmetric De
  Morgan `¬(a∧b) = (¬a ∧ ⊤) ∨ (⊤ ∧ ¬b)` (`¬a` exact, `¬b` reject-safe), proven a
  reject-safe over-approximation (`BehavioralNegation.mixed_negation_soundness`).

This avoids both pitfalls of a literal Rust supertrait chain: no moving method
bodies across the ~13 existing impls, and no `.and()`/`.or()` name ambiguity.

## 6. Decidability tiers and quality

`DecidabilityTier {CompileTimeDecidable/RuntimeDecidable/SemiDecidable/Undecidable}`
(`symbolic.rs:1440`) and the macros `GuardTier {T1Static/T2Decidable/T3Bounded/
T4Assert}` carry the per-guard classification; combination is `max_tier` (the
weakest leg dominates), proven a join-semilattice homomorphism in
`GuardTierCertificate.v`. The tier maps to the documented 7-value **quality**
vocabulary (`docs/architecture/dovetail/04-rules-and-saturation.md`) via
`mettail_rholang_codegen::guard_quality` (T1/T2→`ExactDecidable`, T3→`BoundedDecidable`,
reject-safe→`RejectSafeApprox`, T4→`TrustedNativeGuard`, proof→`MachineCheckedModel`,
runtime→`RuntimeObservation`, undecided→`Unknown`). `Unknown` is fail-closed.

## 7. Concept → code → proof

| Concept | Rust | Zero-admission Coq |
|---|---|---|
| Abstract EBA + laws | `symbolic::BooleanAlgebra` | `EffectiveBooleanAlgebra.v` (`EBA`, `EBA_Laws`, ~28 derived ids) |
| Reject-safe weak law contract | `algebra_tower::RejectSafeAlgebra` | `EffectiveBooleanAlgebra.v` `RejectSafeLaws` + `eba_implies_reject_safe` |
| Product closure | `product_nary::NaryProductAlgebra` | `ProductAlgebraClosure.v` `product_eba_laws` |
| Sum closure | `product_nary::SumAlgebra` | `SumAlgebraClosure.v` `sum_eba_laws` |
| Collection (bag ∀/∃) closure | `collection_algebra::BagAlgebra` | `CollectionAlgebraClosure.v` `collection_eba_laws` |
| Tree closure | `sym_tree::TreeAlgebra` | `TreeAlgebraClosure.v` `tree_eba_laws` |
| Theory combination | `logict::TheoryAlgebra` (union) | `TheoryCombination.v` `combined_eba_laws` |
| ¬¬ closure / reject-safety / H_reg | `algebra_tower::{RejectSafe,Heyting}Algebra` | `HeytingAlgebra.v` |
| Tier lattice ↔ regularity | `symbolic::DecidabilityTier`, macros `max_tier` | `GuardTierCertificate.v` |
| Mixed asymmetric negation | `algebra_tower::RejectSafeProduct` | `BehavioralNegation.v` `mixed_negation_soundness` |

All proofs build under the 32 GiB cap via
`make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-symbolic-algebra` and are
guarded by `formal/scripts/check_rocq_zero_admission.py` (the `symbolic_algebra`
and `sft` theory dirs are in `DEFAULT_ROOTS`); every top theorem's
`Print Assumptions` is `Closed under the global context`.

## 8. Coordination with the Dovetail + Rho backend

This substrate is the **left half** of the boundary: it *classifies* obligations,
it does not lower them.

```
language! → LanguageDef → guard obligations  [collect_guard_obligations — backend.rs]
   → [THIS SUBSTRATE] EBA/SFT/tree/behavioral evidence + quality tag
   → RhoGuardDisposition {kind, quality}  ──fills──▶ RhoGuardCoverageEvidence (fail-closed)
   → [DOVETAIL] guarded rewrite rules + reports → [RHO] AST backend (rhoapi::Par)
```

`guard_quality::derive_guard_qualities(&LanguageDef)` emits the per-obligation
`RhoGuardDispositionQuality` the gate consumes; every emitted disposition is
checked gate-compatible (`backend::guard_disposition_covers`). Proof attribution
stays **external** (commit `6d20b82d`): `MachineCheckedModel` is a quality class,
never a proof-path in `LanguageDef` identity or runtime data.
