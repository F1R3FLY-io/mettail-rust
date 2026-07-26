# Worked Example: GuardedRho End to End

Last updated: 2026-06-22

All symbols are defined in [Concepts and Glossary](01-concepts-and-glossary.md).
This document instantiates the whole suite on one real language. It follows
**GuardedRho** — a minimal rho-calculus-like language whose defining feature is a
guarded receive — from its `language!` declaration, through the substrate's
compile-time classification, to the fail-closed flip gate, to host-routed run-time
enforcement. Every fact below is taken from the shipping source
(`languages/tests/definitions/guarded_rho.rs`), the live planning test
(`languages/tests/guarded_rho_rho_backend.rs`), and the host oracle
(`rholang-runtime/tests/rho_guard_oracle.rs`).

GuardedRho is the canonical example because it exercises the *hardest* case: a
behavioral guard over external relations that is provably **not** lowerable to
Rholang AST, so it must be host-routed — the exact scenario
[08 — Runtime COMM Enforcement](08-runtime-comm-enforcement.md) describes.

## 1. The declaration

GuardedRho declares a guarded receive, two external relations, and a channel/join
block:

```text
PGuardedInput . n:Name, ?guard:Guard, ^x.p:[Name -> Proc]
    |- "for" "(" x "<-" n "where" guard ")" "{" p "}" : Proc ;

guards {
    channels {
        channel Name;
        join PGuardedInput(ch: Name);
    }
}

logic {
    relation halts(Proc);
    relation safe(Proc);
}
```

Three guard surfaces are in play ([06 — Guard Syntax](06-guard-syntax-and-extensions.md)):
the `?guard:Guard` slot on `PGuardedInput`, the `channels { }` sub-block, and the
`logic { }` relations `halts`/`safe` that a user's `where` predicate may query. Here
`halts(P)` and `safe(P)` are **state propositions over a process** — `halts(P)` that
`P` terminates, `safe(P)` that `P` never reaches a bad state — and they are *external*:
"populated by user code," concretized as host-supplied facts rather than computed by
reduction (the closed-world relational mechanism of
[12 §4.2(ii)](12-heyting-behavioral-logic.md#42-the-three-concretization-mechanisms)).
That externality is the crux: the relations are not Rholang-computable.

## 2. Compile-time classification — the substrate's left half

The substrate ([07 §4](07-language-to-rholang-integration.md)) walks the
`LanguageDef` and induces the guard obligations, then classifies each into a
disposition and a quality. These three terms are defined in
[07 §4](07-language-to-rholang-integration.md) and used here as given: an
**obligation** is a unit of guard work induced from the `LanguageDef` (each tagged
with a `RhoGuardObligationKind`, [07 §4.1](07-language-to-rholang-integration.md));
a **disposition** is the run-time *mechanism* chosen to cover it (a
`RhoGuardDispositionKind`, [07 §4.2](07-language-to-rholang-integration.md)); a
**quality** grades *how good* the covering evidence is (a `RhoGuardQuality`, ordered
so `Unknown` is the fail-closed bottom, [07 §4.3](07-language-to-rholang-integration.md)).
`collect_guard_obligations` yields exactly four obligations for GuardedRho:

| Obligation id | `RhoGuardObligationKind` | Source |
|---|---|---|
| `channel:Name` | `RhoNativeJoin` | `channels { channel Name; }` |
| `join:PGuardedInput` | `RhoNativeJoin` | `channels { join PGuardedInput(ch: Name); }` |
| `predicate:standard-builtins` | `BehavioralPredicate` | the builtin-predicate set the `where` guard may use |
| `term:PGuardedInput:guard:guard` | `BehavioralPredicate` | the `?guard:Guard` slot |

Each obligation is then covered by a disposition and graded with a quality. The
live test `guarded_rho_rho_backend.rs` pins the exact dispositions and the resulting
qualities:

| Obligation | Disposition (`RhoGuardDispositionKind`) | Quality (`RhoGuardQuality`) |
|---|---|---|
| `channel:Name` | `RhoNativeJoin` | `RuntimeObservation` |
| `join:PGuardedInput` | `RhoNativeJoin` | `RuntimeObservation` |
| `predicate:standard-builtins` | `EffectiveBooleanAlgebra` | `RejectSafeApprox` |
| `term:PGuardedInput:guard:guard` | `EffectiveBooleanAlgebra` | `RejectSafeApprox` |

The two behavioral legs land on **`RejectSafeApprox`** — the reject-safe quality
([07 §4.3](07-language-to-rholang-integration.md)) of the algebra tower
([05 §5](05-algebra-pyramid-and-decidability.md)), *not* `Unknown`. `RejectSafeApprox`
is the grade the substrate assigns a behavioral leg whose complement is reject-safe
but not classically involutive: it may soundly reject, never wrongly admit — the
Heyting reject-safe evidence whose theory is
[12 — Heyting Behavioral Logic](12-heyting-behavioral-logic.md). This is the test's
load-bearing assertion: every derived quality is non-`Unknown`, and the behavioral
legs are reject-safe. Why reject-safe and not exact? Because a guard like
`where safe(p)` queries the external relation `safe`, which is semi-decidable: the
substrate can soundly reject but cannot classically complement it, so its disposition
carries the Heyting reject-safe evidence
([05 §2](05-algebra-pyramid-and-decidability.md), [12 §6](12-heyting-behavioral-logic.md#6-how-heyting-completes-boolean-for-structural-behavioral-types)).

> **The key derivation — why host-routed is forced, not chosen.** GuardedRho's
> `?guard` is a `RelationQuery` over `halts`/`safe`. The `rhoapi::ReceiveBind` AST
> struct has fields `{patterns, source, remainder, free_count}` — **no guard
> field** — and `halts`/`safe` are external relations that are not Rholang-computable.
> A sound generated-AST lowering of the guarded receive is therefore *impossible*;
> the only sound disposition for the channel/join surfaces is `RhoNativeJoin` — the
> host-routed native-join disposition of
> [07 §4.2](07-language-to-rholang-integration.md), enforced by a host join. This is
> *derived-required*, exactly as [08 §3.3](08-runtime-comm-enforcement.md) describes.

## 3. The fail-closed flip gate

With every obligation covered by a compatible disposition and no `Unknown` quality,
the **fail-closed flip-gate planner** — which admits a language onto the Rho backend
only when every obligation is covered with non-`Unknown` quality, and otherwise
refuses rather than falling through (`plan_rho_default_backend`, the flip gate of
[07 §5](07-language-to-rholang-integration.md)) — admits GuardedRho. The test
exercises both directions of the gate:

> **Algorithm `GuardedRhoFlip` — the gate the test drives.**
>
> ```
> GuardedRhoFlip(def):
>   obligations ← collect_guard_obligations(def)          ▷ the four of §2
>   qualities   ← derive_guard_qualities(def)             ▷ one per obligation
>   if any q in qualities has q.refuses_production_default():   ▷ i.e. Unknown
>     return BLOCKED(RhoFlipBlocker::GuardQuality)        ▷ fail-closed
>   if not exactly_covers(obligations, supplied_dispositions):
>     return BLOCKED                                      ▷ coverage gate
>   return PLAN(language="GuardedRho", dispositions, qualities)
> ```

The test confirms: *without* a coverage supply the audit blocks; *with* the four
exact dispositions of §2 it plans, carrying one quality per obligation, all
non-`Unknown` — so `RhoFlipBlocker::GuardQuality` never fires. The plan records the
two join surfaces as `RuntimeObservation` and the two behavioral legs as
`RejectSafeApprox`, and reports `language_name() = "GuardedRho"` with exactly four
guard-obligation dispositions.

## 4. Run-time enforcement — the host's right half

GuardedRho is now a Rho-default language. At run time a guarded receive
`for (x <- n where safe(x)) { p }` reaches a candidate COMM. Per
[08 — Runtime COMM Enforcement](08-runtime-comm-enforcement.md), enforcement is
host-routed because the guard is behavioral over an external relation:

> **Algorithm `GuardedRhoCommit` — host-routed enforcement.**
>
> ```
> GuardedRhoCommit(candidate σ on channel n):
>   if not name_match(σ):            return rest    ▷ RSpace: channels must meet
>   if not native_join.guard_ok(σ):  return rest    ▷ host join consults `safe`/`halts`
>   if not is_funded(Δ, Σ, margin):  return rest    ▷ funding resource axis (08)
>   return commit                                   ▷ consume input, spawn p[σ]
> ```

The substrate's EBA is **not** re-evaluated here — it already classified the
obligation at compile time. The native join handler consults the external relation
(the same `safe`/`halts` the `logic { }` block declared), and RSpace enforces guard
atomicity: a failed guard leaves the message resting, a later satisfying message
still commits.

That run-time behavior is not asserted but *witnessed*: the host oracle
`rho_guard_oracle.rs` runs real `where`-guarded Rholang against the live f1r3node
`RhoRuntime`, exercising the same "rest, then commit" semantics the native join must
reproduce. These are runtime witnesses, not theorems — they exhibit the guard-atomicity
guarantee on an actual interpreter rather than prove it. The guarantee they witness is
the one proved as a theorem in [08 §3.4](08-runtime-comm-enforcement.md#34-the-guard-atomicity-model-and-its-theorems):
a failed guard commits nothing (`GuardedCommSoundness.v`'s `failed_guard_no_commit`).
Concretely (all in `rholang-runtime/tests/rho_guard_oracle.rs`):

- A `where`-guarded *single* receive whose guard is false leaves the datum resting and
  emits nothing — the rejected datum stays readable on its channel while the body
  channel stays silent (`false_single_bind_guard_leaves_data_and_emits_no_output`).
- Filtering a stream, a *later satisfying* datum fires the receive while the earlier
  failing datum remains available — rejection does not consume
  (`guard_filters_multiple_messages_without_consuming_failed_candidate`).
- A failed *multi-input join* guard leaves all of its join inputs resting — a false
  cross-bind guard consumes none of the inputs it spans
  (`false_cross_bind_guard_leaves_all_join_inputs`).
- A *later satisfying datum still commits without consuming the earlier failed pair* —
  the join's later satisfying inputs commit and are consumed, while the earlier failing
  input remains (`cross_bind_guard_can_commit_later_without_consuming_failed_pair`).

## 5. The end-to-end picture

Reading the trace as the suite's left-to-right spine:

`?guard:Guard + channels{} + logic{halts,safe}  →  4 obligations  →  {RhoNativeJoin ×2, EffectiveBooleanAlgebra ×2}  →  qualities {RuntimeObservation ×2, RejectSafeApprox ×2}  →  fail-closed flip gate PASSES (no Unknown)  →  host-routed native join enforces the guard at COMM time (algebra never re-run)`

GuardedRho is the proof, in one language, of the suite's two crux claims:

1. **The substrate classifies; the host enforces.** The EBA decided coverage and
   quality at compile time; at run time a native join — not generated Rholang and
   not the algebra — gates the COMM ([08](08-runtime-comm-enforcement.md)).
2. **The logic axis composes with the resource axis.** The COMM fires iff the guard
   holds *and* the rewrite is funded ([09 — Funding Composition](09-funding-composition.md)),
   both checked at the boundary. Both are mechanized in the `rho_bridge` Coq theory
   tree — the zero-admission proof tree at `formal/rocq/rho_bridge/theories/` that
   carries the algebra's verdict across the classify-only boundary to a live COMM and
   composes it with the funding discipline and the flip gate (its run-time mirror rows are
   catalogued in [12 §9](12-heyting-behavioral-logic.md#9-the-mechanized-account), its
   full proof matrix in [10 — Formal Verification](10-formal-verification-and-tests.md)).

For the syntax a future GuardedRho author could use to write richer behavioral
guards — `AG safe(q)`, bounded quantifiers, transducer guards — see the proposed
extensions in [06 — Guard Syntax and Extensions](06-guard-syntax-and-extensions.md).
