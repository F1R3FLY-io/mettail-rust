# Dovetail Rewrite Semantics

Last updated: 2026-06-14

This document describes the rewrite semantics Dovetail provides before any
Rho-specific lowering happens. Rho-native execution is valuable only if it
preserves this model.

All symbols used here are defined in
[Concepts and Glossary](01-concepts-and-glossary.md).

## Purpose

Dovetail is the substrate-neutral rewrite engine for MeTTaIL. It answers four
questions:

1. Which terms and equivalence classes exist?
2. Which rewrite facts follow from the language definition?
3. Which normal-form candidates are reachable?
4. Which facts were omitted only because of an explicit bound or external
   contract?

The core invariant is:

`removal(fact) ⇒ evidence(fact)`

Weights may order candidates, but they must not silently prune valid
alternatives.
The rewriting background follows classical term rewriting and confluence
results ([KNUTH-BENDIX-1970](references.md#knuth-bendix-1970),
[HUET-1980](references.md#huet-1980)). Dovetail's equality-maintenance
intuition is close to equality saturation
([EQUALITY-SATURATION-2009](references.md#equality-saturation-2009)), while its
rule iteration has the fixed-point flavor of Datalog evaluation
([DATALOG-BOOK](references.md#datalog-book)).

## Semantic Objects

| Object | Meaning |
|---|---|
| `Term_C` | Terms in category `C`. |
| `Eq_C(t, u)` | Equation fact: `t ≡ u` in category `C`. |
| `Rw_Cᵣ(t, u)` | Rewrite fact: `t →ᵣ u` in category `C`. |
| `Step_C(t)` | Term `t` is scheduled for rewrite exploration. |
| `NF_C(t)` | Term `t` is a normal-form candidate. |
| `Key_C(t, k)` | Exact key `k` identifies term or e-class `t`. |
| `Deriv(d, t, u)` | Derivation witness `d` explains `t →* u`. |

## Rewrite Rule Families

### 1. Seed Rules

The input term becomes an initial fact:

`input(t) ⇒ Term_C(t)`

`Term_C(t) ⇒ Step_C(t)`

This is the entry point for both local Dovetail execution and Rho lowering.

### 2. Equation Closure

Equations form equivalence classes:

`Eq_C(t, u) ⇒ Eq_C(u, t)`

`Eq_C(t, u) ∧ Eq_C(u, v) ⇒ Eq_C(t, v)`

`Eq_C(t, u) ⇒ eclass(t) = eclass(u)`

The equation merges canonical e-class identity; it does not erase the exact
term or derivation keys of the evidence that reached the class. Dovetail keeps
two identities distinct:

| Identity | Meaning | Consumer rule |
|---|---|---|
| `ContentKey(term)` | exact byte identity of a term or derivation record | preserve it in reports and oracle comparisons |
| `EClassId(term)` | canonical equivalence-class representative after merges | use it for congruence closure and rule matching |

Thus equivalent terms may share an e-class while still appearing as distinct
term records when their exact derivation keys differ. A lossy hash may index a
relation, but it must not be the identity proof.

### 3. Directed Rewrites

Each language rewrite contributes a directed step:

`patternᵣ(t, σ) ∧ premisesᵣ(σ) ⇒ Rw_Cᵣ(t, rhsᵣ(σ))`

Here `σ` is a substitution environment. The rule says: if the left-hand pattern
of rule `r` matches term `t`, and every premise of `r` holds under `σ`, then
`t` rewrites to the instantiated right-hand side.

### 4. Equivalence-Respecting Rewrites

Rewriting is closed over equivalence:

`Eq_C(t, t′) ∧ Rw_Cᵣ(t′, u′) ∧ Eq_C(u′, u) ⇒ Rw_Cᵣ(t, u)`

This rule is why equation identity and rewrite reachability cannot be treated
as unrelated subsystems.

### 5. Congruence Rules

If a child rewrites, a parent may rewrite at the child position:

`Rw_A(x, y) ⇒ Rw_C(K(..., x, ...), K(..., y, ...))`

The constructor `K` has result category `C` and a child of category `A`.
Congruence is generated only where the language definition requires it.

### 6. Native and Fold Rules

A native handler is a total-or-explicit-error function from matched inputs to a
result:

`Native_h(args) = Ok(u) ⇒ Rw_C(h(args), u)`

`Native_h(args) = Err(e) ⇒ Rejected(h(args), e)`

Dovetail's coverage proof treats these as external contracts. The Dovetail core
does not prove Rust-native arithmetic correct; it proves that the requirement
is classified and not silently dropped.

### 7. Guarded Rules

A guard is a predicate on a substitution:

`patternᵣ(t, σ) ∧ guardᵣ(σ) = true ⇒ Rw_Cᵣ(t, rhsᵣ(σ))`

`patternᵣ(t, σ) ∧ guardᵣ(σ) = false ⇒ no_commit`

The important property is atomicity: a failed guard must not consume inputs or
hide alternatives.

Predicated types are the language-facing source of these guards. A predicated
type is not a second runtime type system; it is a `language!`-declared guard
constraint that Dovetail receives through generated inventory. The static path
is:

`guards {} + typed predicate signatures + theory registrations + channel declarations → LanguageDef → LanguageMetadata → guarded Dovetail rule`

Dovetail uses that inventory to build `guardᵣ`, `premisesᵣ`, and any external
contract obligations. It must not infer predicated-type meaning from hard-coded
predicate names or category lists. A predicate such as `gt(x: Int, y: Int)` and
a predicate such as `gt(x: Str, y: Str)` may share a surface label, but their
validation and backend contracts are determined by generated typed-predicate
metadata.

The semantic split is:

| Predicated-type layer | Dovetail interpretation |
|---|---|
| structural predicated type | first-order or exact-key match that extends `σ` or fails with `no_commit` |
| structural AC or collection pattern | structural obligation that Dovetail can discharge directly or delegate to SFT evidence |
| behavioral predicated type | predicate over matched values, derived facts, channels, or host state, checked after structural bindings exist |
| EBA-backed predicate | decidable behavioral predicate whose domain supplies effective `⊥`, `⊤`, `∧`, `∨`, `¬`, satisfiability, and witness operations |
| SFT-backed transformation | symbolic transformation or pre-image/post-image obligation, such as normalization before comparison or join-input pruning |
| `logic {}` relation query | premise membership check over the generated language relation inventory |
| quantified or theory-backed predicate | explicit theory/native contract, with boundedness recorded in coverage |
| channel/join declaration | source of multi-premise guarded rule shape and Rho-native atomicity obligation |

The production coverage obligation is:

`∀g ∈ guards(LanguageDef). DovetailCore(g) ∨ EBA(g) ∨ SFT(g) ∨ RhoNetLowerable(g) ∨ NativeGuard(g) ∨ ExternalContract(g) ∨ Rejected(g)`

Thus a guard that is parsed but not classified is a coverage failure, not a
runtime best effort.

### 8. Saturation Rules

The fact set grows monotonically:

`Fᵢ ⊆ Fᵢ₊₁`

`Fᵢ₊₁ = Fᵢ ∪ Δᵢ₊₁`

`Δᵢ₊₁ = derive(Fᵢ, Δᵢ) ∖ Fᵢ`

The fixed point is:

`F* = μF. seed ∪ derive(F, F)`

For finite acyclic rewrite graphs, saturation reaches `F*`. For cyclic graphs,
Dovetail separates exact inside-weight closure from bounded k-best enumeration.

### 9. Extraction Rules

Extraction turns a saturated relation into ordered derivations:

`Deriv(d, t, u) ⇒ Reach(t, u)`

`Reach(t, u) ∧ no_outgoing_rewrite(u) ⇒ NF(u)`

The selection relation preserves all non-refuted candidates:

`candidate(c) ∧ weight(c) ≠ 0̄ ⇒ selected_or_queued(c)`

Weights order extraction. They do not define identity and do not justify silent
candidate removal.
Dovetail's lazy best-first extraction is informed by k-best hypergraph parsing
([HUANG-CHIANG-2005](references.md#huang-chiang-2005)).

## Literate Algorithm: Semi-Naive Saturation

The algorithm below describes the Dovetail fact iteration. It uses deltas to
avoid repeatedly reconsidering only old information.

```pseudocode
Algorithm: Saturate rewrite facts with deltas

Given:
  seed facts F₀
  rewrite rules R
  budget limits B

Produce:
  fact set F
  saturation outcome O

Steps:
  1. Let F be F₀.
     Let Δ be F₀.

  2. While Δ is not empty:
       a. Derive candidate facts N by applying every rule in R to F and Δ.
          At least one premise of each derivation must come from Δ.

       b. Remove facts already present in F.
          The remaining facts are Δ_next.

       c. If adding Δ_next would exceed a node or iteration budget:
            return F with an explicit saturation limit outcome.

       d. Add Δ_next to F.
          Replace Δ with Δ_next.

  3. Return F with outcome Converged.
```

### Invariant

At the start of every loop:

`F = ⋃₀≤j≤i Δⱼ`

and every fact in `F` has a derivation from the seed facts and rules.

### Termination Argument

For finite acyclic fact domains, each iteration adds at least one new fact or
terminates. Since no fact is added twice, the loop terminates after at most the
number of derivable facts.

Saturation termination is enforced by explicit saturation outcomes:

`SatOutcome ∈ {Converged, NodeLimit, IterationLimit}`

Extraction has a separate terminal completeness status:

`ExtractionCompleteness ∈ {Complete, BoundedByCycleCut}`

No bounded extraction outcome is reported as complete. Keeping these status
families separate prevents an implementation from treating a converged
saturation run as proof that a cyclic extraction was exhaustive.

## Literate Algorithm: Exact-Key Deduplication

This algorithm prevents duplicate facts without conflating distinct facts.

```pseudocode
Algorithm: Insert a fact by exact key

Given:
  fact f
  exact key k = key(f)
  fact map M

Produce:
  updated fact map M′
  insertion status S

Steps:
  1. Look up k in M.

  2. If k is absent:
       insert f at k.
       return Inserted.

  3. If k is present with fact g:
       compare f and g by observational equality.

  4. If f and g are observationally equal:
       keep one representative.
       return AlreadyPresent.

  5. Otherwise:
       report an exact-key contract violation.
```

### Invariant

For every key `k` stored in `M`, the facts under `k` are observationally equal:

`M[k] = {f₁, ..., fₙ} ⇒ ∀i,j. fᵢ ≈obs fⱼ`

## Cyclic Closure

Dovetail handles cycles in two layers:

1. inside-weight closure;
2. derivation enumeration.

Inside-weight closure solves recursive weight equations. A simple self-loop has
the form:

`X = a ⊕ b ⊗ X`

When the semiring supports a valid star operation, the least solution is:

`X = b* ⊗ a`

For multi-node strongly connected components, Dovetail delegates the general
Newton-style adequacy to an explicit solver contract and mechanizes the faithful
lowering boundary.
The Newton-style least-fixed-point background is
[NEWTON-MONOTONE-2010](references.md#newton-monotone-2010); the repository-local
formal boundary is listed in [DOVETAIL-FORMAL](references.md#dovetail-formal).

Enumeration is more delicate. Full finite k-best enumeration through arbitrary
productive cycles is impossible in general: a self-cycle with one acyclic exit
has one distinct derivation for each finite unrolling depth. Dovetail therefore
exposes cyclic boundedness:

`cycle_cut_detected ⇒ completeness = BoundedByCycleCut`

`CyclicEnumerationImpossibility.v` proves the finite-exhaustiveness boundary:
no finite list contains every unrolling of a productive self-cycle, so a finite
cyclic extraction must not claim `Complete`. This is a correctness feature, not
a limitation hidden from callers.

## Coverage Taxonomy

Dovetail classifies MeTTaIL requirements into:

| Class | Dovetail responsibility | Rho/backend responsibility |
|---|---|---|
| equations | exact e-class closure | preserve canonical identity |
| directional rewrites | saturation and derivation facts | lower rule firing faithfully |
| congruence | generated parent rewrites | preserve constructor contexts |
| folds/native handlers | classify and call contract | execute deterministic handler |
| structural predicated types | exact-key and pattern matching, or explicit SFT/native contract | preserve match/no-match without consuming hidden alternatives |
| behavioral predicated types | classify dependency and require compatible evidence | implement atomic no-commit on false |
| EBA-backed guards | record theory obligation and coverage evidence | decide predicates over the declared data domain |
| SFT-backed guards | record transducer obligation and coverage evidence | preserve transformation, pre-image, or post-image semantics |
| WFST/selectivity evidence | keep weights/order separate from derivation identity | use only for scheduling or ordering, never candidate deletion |
| collections/patterns | pattern lowering requirements | preserve arity and binding |
| cyclic weights | inside-weight closure | preserve reported boundedness |
| ambiguity | candidate-set preservation | avoid scheduler-choice collapse |
| Rho contracts | external contract | prove operational correspondence |

The key coverage formula is:

`∀req ∈ Requirements(L). Covered(req) ∨ Rejected(req, reason) ∨ ExternalContract(req)`

## Why This Matters for Rho

The Rho backend is not allowed to be “best effort.” It must preserve Dovetail's
fact semantics:

`lower(F*) = resting(Rho(lower(F₀)))`

up to the documented observation quotient. The following documents explain how
that equality is achieved by compiling facts and rules into a Rho-native
dataflow network.
