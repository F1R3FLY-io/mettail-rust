# Runtime COMM Enforcement

Last updated: 2026-06-22

All symbols are defined in [Concepts and Glossary](01-concepts-and-glossary.md).
This document answers the single most-asked and most-misunderstood question about
the substrate: **once a language has been dispatched, how is a semantic predicate
enforced at run time — and what, exactly, does Rholang do?** The honest answer is
the spine of this page, so it is stated immediately and then justified.

## 1. The honest answer, up front

> **Rholang does not evaluate the semantic-predicate algebra at run time.** The
> prattail EBA/SFA/SFT substrate runs entirely at **compile time** and is
> classify-only ([07](07-language-to-rholang-integration.md)). At run time the
> *surviving* guard is enforced by the host in one of three ways, none of which
> re-runs the algebra:
>
> 1. **structural** guards, via RSpace **spatial pattern matching**;
> 2. **pure boolean** guards over bound ground values, via a Rholang **`where`
>    receive guard** that F1r3node evaluates before commit;
> 3. **everything richer** (effective-theory, transducer, behavioral, multi-channel
>    join), via a **host-routed native join** (`RhoNativeJoin`) that gates the COMM
>    at the RSpace boundary.

Admission is decided *before* run time by the fail-closed flip gate of
[07 §5](07-language-to-rholang-integration.md): a language only runs on the Rho
backend if every guard obligation was covered with non-`Unknown` quality. So "how
Rholang applies the semantic predicate" is, precisely: **it doesn't apply the
algebra at all** — it matches structure, it may evaluate a simple `where` boolean,
and it defers everything else to a host gate. What is *guaranteed* at run time is
**guard atomicity**: a failed guard consumes nothing and emits nothing.

![Runtime COMM enforcement: where each predicate class is gated](figures/08-comm-enforcement.svg)

PlantUML source: [figures/08-comm-enforcement.puml](figures/08-comm-enforcement.puml).

## 2. What a COMM is, and what "enforcement" means

A Rholang communication — a **COMM** — is the meeting of a receive `for(P <- c)`
and a send `c!(Q)` on a shared channel `c`. When they meet, RSpace atomically
consumes the message and spawns the continuation with the receive's pattern bound.
A *guarded* COMM additionally requires a predicate to hold before it may commit.
"Enforcement at run time" means exactly this: deciding, at the moment a candidate
COMM is enabled, whether the guard permits the commit — and, if not, leaving the
data resting so a later candidate can still fire.

The mechanized semantics make the requirement precise. The firing condition is

`comm_fires(σ) = name_match(σ) ∧ structural_eval(σ) ∧ behavioral_eval(σ)`

— a candidate substitution `σ` fires iff the channel names match, the structural
predicate holds, and the behavioral predicate holds. Three results pin the gate down,
each stated here and proved in its own home (the run-time COMM model
`RhoGuardedCommSoundness.v`, zero-admission):

**Result 2.1 (the COMM gate is exactly the guard).** A guarded rule commits under `σ`
iff `comm_fires(σ)` holds — `name_match(σ) ∧ structural_eval(σ) ∧ behavioral_eval(σ)`.
This biconditional is the characterization of when a guarded rule may fire; both
directions are mechanized in `RhoGuardedCommSoundness.v` (`comm_fires_iff`), with the
positive direction — a satisfied guard over matching names *does* commit — separately
recorded as `rho_guard_true_commits`. The negative direction is **Result 2.2**.

**Result 2.2 (a complemented guard never commits).** If the guard's behavioral leg
holds *because its reject-safe complement holds* — a `DontKnow`/complemented behavioral
verdict — then `comm_fires(σ) = false` and no COMM fires. This is the run-time mirror of
the **asymmetric mixed De Morgan reject-safety** proved as
[12 — Heyting Behavioral Logic, Theorem 6.1](12-heyting-behavioral-logic.md#6-how-heyting-completes-boolean-for-structural-behavioral-types)
(`mixed_negation_soundness`); its COMM-boundary form is `RhoGuardedCommSoundness.v`'s
`rho_complement_no_commit`. It is **not re-proved here** — §5 item 1 below explains why a
semi-decidable guard must be reject-safe, and the algebraic content is doc 12's.

Crucially, the model treats `structural_eval` and `behavioral_eval` as **abstract**
boolean functions on `σ`: Result 2.1 *fixes the semantics* ("fires iff guard holds"),
while the *realizations* of those abstract functions at run time are exactly the three
concretization mechanisms of
[12 §4.2](12-heyting-behavioral-logic.md#42-the-three-concretization-mechanisms)
(model-check over a `HostTerm` LTS / closed-world `FactBase` / host observation at COMM
time) — cross-referenced there, not restated — projected onto the three enforcement
mechanisms of §3.

## 3. The three enforcement mechanisms

### 3.1 Structural guards — RSpace spatial matching

A structural predicate (`AcMatch`, a constructor pattern, a refinement of shape) is
enforced by RSpace's own pattern matching. A receive `for(@Pattern <- c)` is enabled
only when an incoming term *structurally matches* `Pattern`. This is native,
atomic, and free — it is what RSpace already does — but it can express only the
*shape* of data, never a value- or behavior-level property like "`x` is prime" or
"`P` halts."

This is the `DovetailCoreStructural` disposition reaching run time as ordinary
Rholang/RSpace matching.

### 3.2 Pure boolean guards — the Rholang `where` clause

Rholang supports a receive guard directly in the surface language:

```rholang
for (@x <- @"c" where x > 0) { @"OUT"!(x) }
```

F1r3node's `RhoRuntime` evaluates the `where` clause **before commit**, and the
behavior is exactly guard atomicity. This is verified live, not asserted, by
`rholang-runtime/tests/rho_guard_oracle.rs`:

| Test | What it proves |
|---|---|
| `false_single_bind_guard_leaves_data_and_emits_no_output` | a failed `where` guard emits no body and leaves the rejected datum resting |
| `guard_filters_multiple_messages_without_consuming_failed_candidate` | a later satisfying datum fires the receive; the earlier failing datum stays available |
| `false_cross_bind_guard_leaves_all_join_inputs` | a failed cross-bind join guard (`for (@x <- @"a" & @y <- @"b" where x + y > 10)`) consumes no join input |
| `cross_bind_guard_can_commit_later_without_consuming_failed_pair` | the later satisfying pair commits and consumes its inputs; the earlier failing input remains |

These run real Rholang source on the host RSpace and validate the guard-atomicity
theorems of §3.4 — in particular **Theorem 3.1** (`failed_guard_no_commit`) — against an
actual interpreter.

> **The boundary that forces host-routing.** The `where` clause is enforceable when
> the predicate is a pure boolean over bound ground values *and the program is
> expressed as Rholang source*. MeTTaIL's production Rho lane builds `rhoapi::Par`
> **AST directly** (no source round-trip), and the `rhoapi::ReceiveBind` struct it
> constructs has fields `{patterns, source, remainder, free_count}` — **no guard
> field**. So MeTTaIL cannot emit a literal `where` through the AST path; a guard
> that cannot be folded into the match pattern is therefore routed to the native
> join of §3.3. The `where` oracle proves the *semantics* the native join must
> reproduce.

### 3.3 Everything richer — the host-routed native join (`RhoNativeJoin`)

An effective-theory predicate (a Presburger formula), a transducer relation, or a
**behavioral** predicate over external relations (`halts`, `safe`) is **not
Rholang-computable**: Rholang cannot decide a linear-integer formula, run an SFT, or
query a host relation, and — per §3.2 — cannot even carry a guard field in the AST
it is handed. These guards take the `RhoNativeJoin` disposition.

At run time a **native join handler** sits at the RSpace COMM boundary. When a
candidate join is enabled, the handler decides whether the guard permits the commit
(consulting the host relation, evaluating the theory, or running the transducer),
and either lets RSpace commit or leaves the inputs resting. The predicate algebra is
**not** re-evaluated here either — the substrate already classified the obligation
at compile time and the gate already admitted it; the handler enforces the
*decision*, using host facilities, with the same non-consuming-on-false semantics.

GuardedRho is the canonical instance: its `?guard` is a `RelationQuery` over the
external relations `halts`/`safe` "populated by user code"
(`languages/src/guarded_rho.rs`). Because `rhoapi::ReceiveBind` has no guard field
and external relations are not Rholang-computable, a sound generated-AST lowering of
the guarded receive is *impossible* — host-routing via `RhoNativeJoin` is
**derived-required**, not a preference. The worked trace is
[11 — Worked Example](11-worked-example.md).

### 3.4 The guard-atomicity model and its theorems

All three mechanisms of §3.1–§3.3 share one run-time guarantee — **guard atomicity** —
and that guarantee is what is proved here. The proof-home is the guarded-COMM model
`GuardedCommSoundness.v` (zero-admission), which abstracts an RSpace receive guard, or a
native guard handler, to its essential decision: given the current facts, either commit
the rule's output atomically or leave the store untouched. This is the model the §3.2
`where` oracle validates against a live interpreter, and the decision a §3.3
`RhoNativeJoin` handler enforces with host facilities; the theorems below hold uniformly
across all three mechanisms.

**Definition 3.2 (the guarded-COMM model).** A **fact store** is a finite set of facts.
A **guarded rule** `r` carries three components: a list of **premises** `premises(r)`, a
boolean **guard** `guard(r)`, and an **output fact** `output(r)`. Write
`all_present(facts, premises)` for the predicate "every premise of `premises` is in
`facts`", and `insert_exact(f, facts)` for the store that adds `f` to `facts` if absent
and is `facts` unchanged otherwise. The relation `guarded_attempt(facts, r, next)`
("attempting `r` against `facts` yields store `next`") is **inductive with exactly three
constructors**:

| Constructor | Precondition | Result `next` |
|---|---|---|
| **commit** | `all_present(facts, premises(r))` ∧ `guard(r) = true` | `insert_exact(output(r), facts)` |
| **reject-guard** | `all_present(facts, premises(r))` ∧ `guard(r) = false` | `facts` (unchanged) |
| **reject-missing** | `¬ all_present(facts, premises(r))` | `facts` (unchanged) |

The three constructors are mutually exhaustive on the two boolean dimensions (all
premises present or not; guard true or false), so every attempt lands in exactly one
case — and only **commit** modifies the store. Mechanized in `GuardedCommSoundness.v` as
the record `GuardedRule` and the inductive `guarded_attempt`, with `all_present` and
`insert_exact` as above. This is exactly RSpace's "consume-and-spawn iff the guard
permits" reduced to the one bit that the soundness argument turns on. The two
characterizing theorems are the negative gate (a failed guard changes nothing) and the
positive gate (a satisfied guard over present premises delivers the output).

**Theorem 3.1 (a failed guard commits nothing).** If `guard(r) = false` and
`guarded_attempt(facts, r, next)`, then `next = facts`.

*Proof.* Invert the derivation of `guarded_attempt(facts, r, next)` (Definition 3.2):
it was built by exactly one of the three constructors. The **commit** constructor is
impossible here — it requires `guard(r) = true`, contradicting the hypothesis
`guard(r) = false`. The remaining two constructors, **reject-guard** and
**reject-missing**, each conclude with `next = facts` by construction. So in every
possible case `next = facts`. `∎` (Mechanized as `failed_guard_no_commit`.)

**Theorem 3.2 (a satisfied guard over present premises commits the output).** If
`all_present(facts, premises(r))` and `guard(r) = true`, then there exists a store
`next` with `guarded_attempt(facts, r, next)` and `output(r) ∈ next`.

*Proof.* Take `next := insert_exact(output(r), facts)`. Both hypotheses
`all_present(facts, premises(r))` and `guard(r) = true` are exactly the preconditions of
the **commit** constructor (Definition 3.2), which therefore derives
`guarded_attempt(facts, r, insert_exact(output(r), facts))`. And
`output(r) ∈ insert_exact(output(r), facts)`: by definition of `insert_exact`, the
inserted fact is a member of the result whether or not it was already present. Hence the
witnessed `next` satisfies both conjuncts. `∎` (Mechanized as
`true_guard_enabled_adds_output`.)

Two further properties sharpen the no-commit guarantee, and §4 and §5 cite them:

**Theorem 3.3 (no fabrication).** If `guarded_attempt(facts, r, next)` and `x ∈ next`,
then `x = output(r)` or `x ∈ facts`. A guarded attempt never invents a fact other than
the rule's declared output.

*Proof.* Invert the attempt (Definition 3.2). In the **reject-guard** and
**reject-missing** cases `next = facts`, so `x ∈ next` gives `x ∈ facts` directly. In the
**commit** case `next = insert_exact(output(r), facts)`; by the membership law of
`insert_exact`, any `x ∈ insert_exact(output(r), facts)` is either `x = output(r)` or
`x ∈ facts`. All three cases discharge the disjunction. `∎` (Mechanized as
`guarded_attempt_no_fabrication`, over the supporting lemma `insert_exact_membership`.)

**Theorem 3.4 (a missing premise commits nothing).** If
`¬ all_present(facts, premises(r))` and `guarded_attempt(facts, r, next)`, then
`next = facts`.

*Proof.* Invert the attempt (Definition 3.2). The **commit** and **reject-guard**
constructors both require `all_present(facts, premises(r))`, contradicting the
hypothesis, so neither applies; the only available case is **reject-missing**, whose
conclusion is `next = facts`. `∎` (Mechanized as `missing_premise_no_commit`.)

Together Theorems 3.1, 3.3, and 3.4 are the formal content of "a failed guard consumes
nothing and emits nothing," and Theorem 3.2 is its dual — "a satisfied guard does
deliver the output." These are the run-time guarantee the §1 summary promised; the §4
matrix and §5 architecture rest on them.

## 4. What generated Rholang does and does not do

| Concern | Done by generated Rholang? | Done by | Evidence |
|---|---|---|---|
| structural shape match | yes (RSpace patterns) | RSpace | structural disposition |
| pure boolean over ground values, source path | yes (`where`) | F1r3node `where` eval | `rho_guard_oracle.rs` |
| pure boolean, AST path | no (no guard field) | host-routed native join | `rhoapi::ReceiveBind` shape |
| effective-theory predicate (Presburger, intervals) | no | compile-time classification + host gate | [02](02-effective-boolean-algebra.md), `RhoNativeJoin` |
| transducer relation (SFT/STFT) | no | compile-time classification + host gate | [04](04-symbolic-transducers-sft-stft.md) |
| behavioral predicate (`halts`/`safe`, modal) | no (not Rholang-computable) | host native join | `guarded_rho.rs`, `rho_guard_oracle.rs` |
| guard atomicity (no-commit-on-false) | enforced for all of the above | RSpace + handler | §3.4 Theorems 3.1–3.4 (`GuardedCommSoundness.v`) |

The pattern is uniform: **Rholang/RSpace enforces structure and simple booleans;
the host gate enforces everything the algebra classified; the algebra itself never
runs at run time.**

## 5. Why this division is the correct architecture

It is not a limitation worked around — it is the soundness boundary of
[05 — Algebra Pyramid](05-algebra-pyramid-and-decidability.md) projected onto run
time:

1. **Semi-decidable predicates must not be evaluated speculatively in the hot
   path.** A behavioral guard is reject-safe precisely because a bounded search can
   say `DontKnow`; embedding that search in a COMM commit would either block the
   scheduler or risk a false fire. Classifying it at compile time and gating it with
   a host handler keeps the run-time COMM decision *total and fast*.
2. **The decidable predicates are already decided.** An `ExactDecidable` or
   `BoundedDecidable` obligation was settled by the substrate before run time; the
   run-time job is to *match structure* or *consult the recorded decision*, not to
   re-derive it.
3. **Admission is fail-closed.** A language with any `Unknown`-quality obligation
   never reaches run time on the Rho backend, so the run-time mechanisms only ever
   face obligations that *were* coverable.
4. **Atomicity is the one universal run-time guarantee.** Whatever the mechanism, a
   failed guard consumes nothing and emits nothing (§3.4 Theorem 3.1), a missing premise
   likewise (Theorem 3.4), no fact is fabricated (Theorem 3.3), and a later satisfying
   candidate can still commit (Theorem 3.2). That is the property a developer can rely on
   regardless of how a particular guard is enforced.

The resource axis this gate composes with — *a COMM fires iff the guard is
satisfied **and** the rewrite is funded* — is
[09 — OSLF Composition](09-oslf-composition.md).
