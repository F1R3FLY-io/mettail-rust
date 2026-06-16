# Ambient in-engine binder + freshness lowering — Red-team Round 1 (REFUTED v1) + corrected constraints

## What v1 (Strategy C) proposed, and why it was REFUTED

v1 proposed lowering Ambient's `PNew ^x.P` binder + freshness equations in-engine by
(1) name-erasing the binder to a de-Bruijn `ENode`, (2) checking freshness via
`RhocalcAstLowering.v::filter_adjust` (a de-Bruijn-index occurrence scan), and
(3) realizing `NewComm` as a `bind_index`-based transposition of the two outer binders.

A soundness red-team **REFUTED all three load-bearing claims** against source:

- **CLAIM-3 (freshness = `filter_adjust`) REFUTED.** `filter_adjust`
  (`formal/rocq/rho_bridge/theories/RhocalcAstLowering.v:354-369`) is **dead code** —
  zero call sites, just trims the first `bind_count` elements of a `list bool`; it has
  no connection to free-variable occurrence and there is no theorem relating it to
  `x ∉ free(P)`. The **real** freshness reference is moniker `free_vars`:
  `macros/src/logic/rules.rs:959-990` — `!BoundTerm::free_vars(&P).contains(&x)` (Var)
  and `rest.iter().all(|(e,_)| !free_vars(e).contains(&x))` (CollectionRest). **Confirmed
  by direct Read.** Worse, a de-Bruijn-*index* freshness check is **capture-unsound over
  the AC-bag complement**: a de-Bruijn index is meaningful only relative to its binder
  depth, the same source name sits at different indices in members at different nesting
  depths, and bag members are interned without a shared binder context — so an index scan
  can give FALSE "fresh" (admitting capture) or FALSE "not fresh" (blocking a valid
  extrusion). The shipped `free_vars().contains(&FreeVar)` is immune (FreeVar identity is
  position-independent).

- **CLAIM-4 (NewComm = `bind_index` transposition) REFUTED.** `bind_index n i = n-1-i`
  (RhocalcAstLowering.v:91, 318-320) is **receive-binder order** (`PInput2`), nothing to do
  with `new`; `lower_proc` has no `ANew`-producing arm. Swapping two nested single-binders
  is **not** a node swap — every bound occurrence in the body must be re-indexed
  (`ScopeOffset 0 ↔ 1`); a node-only swap is involutive but **semantically wrong** for any
  body that mentions the binders. The reference compiles NewComm via `unbind()` +
  fresh-var alpha-rename + `multi_substitute` (`macros/src/logic/rules.rs:2397-2404`), not
  index transposition.

- **CLAIM-1 (alpha = ContentKey via blanket name-erasure) REFUTED-as-written, idea
  salvageable.** moniker's `BoundVar` Eq/Hash already ignore `pretty_name` (compare/hash
  `scope`+`binder` only), so the de-Bruijn *core* is clean. BUT the current `binder_arm`
  (`macros/src/gen/runtime/dovetail_report.rs:198-249`, **confirmed by Read**) does the
  *opposite* of erasure: the binder child is `format!("{}::{:?}", binder_label,
  scope.unsafe_pattern())` (prints name + `unique_id`), and the body's `Var` leaves are
  lowered by the `category_lowering` Var arm (`:256-262`) as `format!("{}::{:?}", owner,
  value)` for **both** `Var::Bound` and `Var::Free` uniformly. So today `new(x,x)` and
  `new(y,y)` get **different** keys. A *blanket* name strip would be **unsound** — it would
  conflate distinct **free** vars (`new(x,z)` vs `new(x,w)`). **Narrowing:** the alpha
  defect is ONLY in (i) bound occurrences and (ii) the binder position; **free occurrences
  are already correctly keyed** (their `{:?}` is the FreeVar identity = moniker Eq/Hash).
  So the correct fix discriminates `Var::Bound` (key by `(scope,binder)` only) from
  `Var::Free` (keep the identity key), and strips only the binder *position* name.

- **"Datalog eqrel is the reference" framing REFUTED.** The Ascent eqrel **skips
  binder-bearing constructors and collections** (`macros/src/logic/equations.rs:271-283`).
  The genuine reference oracle for binder/freshness behavior is the moniker **rewrite
  path** (`unbind`/alpha-rename + `free_vars`), i.e. what `run_ascent` actually executes —
  NOT the eqrel.

## Corrected constraints the v2 design MUST satisfy

1. **Freshness uses moniker `free_vars` *identity* semantics**, never a de-Bruijn-index
   occurrence scan. The check must be position-independent and capture-safe exactly as
   `rules.rs:976/:986`. (Open: lift it to the e-graph as a lazy/memoized free-var-identity
   set, OR re-derive from leaf keys — see the elegance note below.)
2. **Alpha = ContentKey by discriminating Bound vs Free**, not blanket erasure: `Var::Bound`
   → `(scope,binder)` coordinates only; `Var::Free` → keep identity key; binder *position*
   name stripped. Prove `alpha_equiv ⟺ equal_key` for the single-sort Ambient binder; keep
   `new(x,z) ≢ new(x,w)`.
3. **The reference oracle is the moniker rewrite path** (`unbind`/alpha-rename + `free_vars`
   via `run_ascent`), not the eqrel. The differential corpus must be `new`/scope-extrusion
   terms and compare against `run_ascent`'s actual normal forms.
4. **NewComm, if realized in-engine, re-indexes the body** (`ScopeOffset 0↔1`) and proves
   *that* — with a NEW small self-contained theorem, NOT by reusing `bind_index`. May be
   staged last / gated on whether the corpus exercises adjacent-`new` commutation. Reusing
   the reference's `unbind`+rename is also admissible.
5. **No false reuse of `RhocalcAstLowering.v`.** That theory models rho-calculus
   receive-binders and contains NO `PNew`/`ANew`, no freshness predicate, no alpha theorem.
   Any binder/freshness/swap proof is NEW, self-contained, zero-admission.

## The de-Bruijn elegance worth resolving (the v2 fork)

After erasure, bound occurrences are `db::(scope,binder)` leaves and free occurrences are
`fv::identity` leaves. So **the free variables of a class = the set of `fv::` leaf
identities reachable in it** — no binder-aware subtraction at lookup, because erasure
already split bound (`db::`) from free (`fv::`). This makes `x # P` a simple
identity-keyed leaf scan (lazily memoizable), capture-safe (bound occurrences are never
`fv::`) and position-independent. **This is the e-graph-native form of moniker
`free_vars`** and the recommended freshness realization.

But a genuine fork remains on scope-extrusion mechanics:

- **(V2-a) Named + `free_vars` guard.** Keep source identities; ScopeExtrusion carries an
  `fv::id`-set freshness guard (`x # rest`) on `RewriteRule`, checked in `saturate` before
  `merge`. Mirrors the reference directly. The binder's source identity is still available
  from `unsafe_pattern()` at lowering even though the body key erases it.
- **(V2-b) Locally-nameless de-Bruijn.** Alpha-collapse binders to coordinates; scope
  extrusion becomes an index-*shift* on the extruded `rest` (free indices +1 under the new
  binder), and the freshness premise vanishes (de-Bruijn never captures — discharged
  *structurally*). More elegant; but the shift reintroduces an index-manipulation proof
  obligation (the same family CLAIM-4 warned about — must be proven, not assumed).

The v2 design must **resolve this fork with code grounding** (which is sound AND
minimal-proof AND aligned with the three mandates: ambiguity-preserving, lazy,
WPDA-integrated), then specify exact engine changes + zero-admission Rocq + staged
increments + tests + the corrected differential oracle.

## Confirmed code facts (anchor the v2 design here)
- `macros/src/gen/runtime/dovetail_report.rs:198-249` — `binder_arm`, prints names (`{:?}`).
- `macros/src/gen/runtime/dovetail_report.rs:256-262` — `category_lowering` Var arm, `{:?}`
  for both Bound and Free.
- `macros/src/gen/runtime/dovetail_report.rs:383-392/:402-409/:415-418` — the rejection sites.
- `macros/src/logic/rules.rs:959-990` — `generate_freshness_clause` = real `free_vars` ref.
- `macros/src/logic/rules.rs:2395-2440` — binder-equation `unbind`/alpha-rename rewrite ref.
- `macros/src/logic/equations.rs:271-283` — eqrel skips binders + collections.
- `formal/rocq/rho_bridge/theories/RhocalcAstLowering.v:354-369` — `filter_adjust` dead;
  `:91/:318-320` — `bind_index` receive-order; no `PNew`/`ANew`/freshness/alpha anywhere.
- `runtime/src/binding.rs` — moniker `Scope`: `unsafe_pattern()` retains the binder FreeVar
  identity; `unsafe_body()` is the closed (de-Bruijn) body; `BoundVar` Eq/Hash ignore name.
- `dovetail/src/{egraph.rs,rules.rs}` — `ENode`/`content_key` hashcons; `Pattern` matcher +
  `saturate`; the P4 AC machinery (`Pattern::AcApp`, `add_flattened_bag`) to integrate with.
