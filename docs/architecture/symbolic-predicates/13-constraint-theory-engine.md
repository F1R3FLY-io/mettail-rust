# The Constraint-Theory Engine: LogicT Under the Substrate

Last updated: 2026-06-22

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

The three shipped theories — `PresburgerTheory`, `UnificationTheory`,
`LatticeTheory` — return an empty `label` (decidable: propagation only, the
`search_bound` is irrelevant), except `UnificationTheory`'s extended custom-match,
whose non-empty `label` engages the fair search bounded by `search_bound` (the
`LT01` lint guards it). `PresburgerAlgebra` additionally has a *direct*
`BooleanAlgebra` path (NFA-backed, [02 §5](02-effective-boolean-algebra.md)) for
speed, distinct from the bridge.

## 3. Quantified-predicate evaluation

A `∀x ∈ dom. φ` or `∃x ∈ dom. φ` guard ([06 §2.3.1](06-guard-syntax-and-extensions.md))
is where the engine most visibly meets the predicate substrate.

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

> **Accuracy: where the monad is literal and where it is semantic.** The two-valued
> `evaluate_quantified` recurses over the materialized tuples from `domain_enumerate`
> with `all`/`any` and a `Bounded` domain's `min(limit, default_bound)` truncation —
> it does not construct a `LogicStream` per quantifier. The logic monad backs
> `TheoryAlgebra::witness` and `multiset_partitions` *literally* (fair search), and
> backs the quantifier evaluator *semantically*: the closed-world `∀x. φ ≡ ¬∃x. ¬φ`
> identity is the `gnot` equivalence, and the bounded enumeration mirrors
> `collect_bounded`. The fairness of §1 matters at the `witness` layer beneath a
> theory-guided quantifier, not in the plain enumeration.

## 4. Theory combination — the Nelson–Oppen base case

Two decidable theories over a shared enumerable domain combine into one EBA by
**joint search**: the LogicT realization interleaves their constraint streams and
labels under the bounded budget.

![Two constraint theories combine by joint interleaved search](figures/13-theory-combination.svg)

PlantUML source: [figures/13-theory-combination.puml](figures/13-theory-combination.puml).

The formal counterpart is `TheoryCombination.v` (`combined_eba_laws`, with
`csat_sound`/`csat_complete`, [10 §2.1](10-formal-verification-and-tests.md)). This
is the **base case** of [Nelson & Oppen, 1979](references.md#nelson-oppen-1979) —
joint search over a shared domain — *not* the full equality-exchange procedure, and
the documentation says so rather than implying it. The proposed `arithmetic <+> text`
syntax ([06 §3.8](06-guard-syntax-and-extensions.md)) is the surface for it.

## 5. Enforcement of predicated types

The engine is where a quantified or theory guard earns its **tier** and **quality**,
which the fail-closed gate ([07 §5](07-language-to-rholang-integration.md)) acts on:

| How the LogicT evaluation terminates | Tier | Quality |
|---|---|---|
| finite-relation quantifier / decidable theory (propagation decides; `label = empty`) | T1 / T2 | `ExactDecidable` |
| bounded quantifier or `search_bound`-limited labeling that returned a definite verdict | T3 | `BoundedDecidable` |
| `evaluate_quantified_with_theory → Unknown` (budget exhausted, `had_unknown`), or `collect_bounded` truncated without a witness (`LT01`) | maps to `Sat3::DontKnow` | fail-closed unless asserted (`#[tier(t4)]` / `@[quality(trusted)]`) |

Two places turn the engine's "don't know" into a *rejection*, never a false
admission: `into_safe_bool` (`Unknown → false`) and the bridge's
`is_satisfiable = witness().is_some()`. Both are the operational realization of the
reject-safe discipline ([05 §5](05-algebra-pyramid-and-decidability.md),
`mixed_negation_soundness`), and they connect directly to `classify_quality`'s
`behavioral → reject-safe` rule ([07 §4.3](07-language-to-rholang-integration.md))
and the flip gate's block on `Unknown`. The decidability-tier lattice (
[05 §6](05-algebra-pyramid-and-decidability.md), `GuardTierCertificate.v`) is the
formal frame; `collect_bounded(search_bound)` plus the `LT01` lint is the resource
meter that decides which tier a given guard lands in.

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

| Claim | Where |
|---|---|
| theory combination is an EBA (Nelson–Oppen base case) | `TheoryCombination.v` (`combined_eba_laws`, `csat_sound`, `csat_complete`) — [10 §2.1](10-formal-verification-and-tests.md) |
| the bridge soundness (a covered theory guard never false-fires) | `BehavioralNegation.v` (`mixed_negation_soundness`) — [10 §2.1](10-formal-verification-and-tests.md) |
| the tier ↔ regularity / decidability frame the engine populates | `GuardTierCertificate.v` — [05 §6](05-algebra-pyramid-and-decidability.md), [12 §5](12-heyting-behavioral-logic.md) |
| the bounded-search lint | `prattail/docs/diagnostics/logict/LT01.md` (`logict-search-bound-exceeded`) |
| full API + algorithms (msplit, interleave, fair_conjoin, witness, evaluate_quantified) | `prattail/docs/design/constraint-theories/logict-framework.md` |

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
