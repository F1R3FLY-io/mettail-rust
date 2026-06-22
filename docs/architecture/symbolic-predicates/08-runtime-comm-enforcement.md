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

The mechanized semantics make the requirement precise. In
`RhoGuardedCommSoundness.v` the firing condition is:

`comm_fires(σ) = name_match(σ) ∧ structural_eval(σ) ∧ behavioral_eval(σ)`

— a candidate substitution `σ` fires iff the channel names match, the structural
predicate holds, and the behavioral predicate holds. The theorem `comm_fires_iff`
characterizes exactly when a guarded rule commits; `rho_complement_no_commit` and
`rho_guard_true_commits` prove the two directions of the gate. Crucially, the model
treats `structural_eval` and `behavioral_eval` as **abstract** boolean functions on
`σ`: the *theorem* fixes the semantics ("fires iff guard holds"), while the three
mechanisms of §3 are the *realizations* of those abstract functions at run time.

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

These run real Rholang source on the host RSpace and validate `GuardedCommSoundness.v`'s
`failed_guard_no_commit` against an actual interpreter.

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

## 4. What generated Rholang does and does not do

| Concern | Done by generated Rholang? | Done by | Evidence |
|---|---|---|---|
| structural shape match | yes (RSpace patterns) | RSpace | structural disposition |
| pure boolean over ground values, source path | yes (`where`) | F1r3node `where` eval | `rho_guard_oracle.rs` |
| pure boolean, AST path | no (no guard field) | host-routed native join | `rhoapi::ReceiveBind` shape |
| effective-theory predicate (Presburger, intervals) | no | compile-time classification + host gate | [02](02-effective-boolean-algebra.md), `RhoNativeJoin` |
| transducer relation (SFT/STFT) | no | compile-time classification + host gate | [04](04-symbolic-transducers-sft-stft.md) |
| behavioral predicate (`halts`/`safe`, modal) | no (not Rholang-computable) | host native join | `guarded_rho.rs`, `rho_guard_oracle.rs` |
| guard atomicity (no-commit-on-false) | enforced for all of the above | RSpace + handler | `GuardedCommSoundness.v` |

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
   failed guard consumes nothing and emits nothing (`failed_guard_no_commit`), and a
   later satisfying candidate can still commit. That is the property a developer can
   rely on regardless of how a particular guard is enforced.

The resource axis this gate composes with — *a COMM fires iff the guard is
satisfied **and** the rewrite is funded* — is
[09 — OSLF Composition](09-oslf-composition.md).
