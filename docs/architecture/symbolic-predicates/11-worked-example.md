# Worked Example: GuardedRho End to End

Last updated: 2026-06-22

All symbols are defined in [Concepts and Glossary](01-concepts-and-glossary.md).
This document instantiates the whole suite on one real language. It follows
**GuardedRho** — a minimal rho-calculus-like language whose defining feature is a
guarded receive — from its `language!` declaration, through the substrate's
compile-time classification, to the fail-closed flip gate, to host-routed run-time
enforcement. Every fact below is taken from the shipping source
(`languages/src/guarded_rho.rs`), the live planning test
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
`logic { }` relations `halts`/`safe` that a user's `where` predicate may query. The
relations are *external* — "populated by user code" — which is the crux: they are
not Rholang-computable.

## 2. Compile-time classification — the substrate's left half

The substrate ([07 §4](07-language-to-rholang-integration.md)) walks the
`LanguageDef` and induces the guard obligations, then classifies each into a
disposition and a quality. `collect_guard_obligations` yields exactly four
obligations for GuardedRho:

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

The two behavioral legs land on **`RejectSafeApprox`** — the reject-safe quality of
the algebra tower ([05 §5](05-algebra-pyramid-and-decidability.md)), *not* `Unknown`.
This is the test's load-bearing assertion: every derived quality is non-`Unknown`,
and the behavioral legs are reject-safe. Why reject-safe and not exact? Because a
guard like `where safe(p)` queries the external relation `safe`, which is
semi-decidable: the substrate can soundly reject but cannot classically complement
it, so its disposition carries the Heyting reject-safe evidence
([05 §2](05-algebra-pyramid-and-decidability.md)).

> **The key derivation — why host-routed is forced, not chosen.** GuardedRho's
> `?guard` is a `RelationQuery` over `halts`/`safe`. The `rhoapi::ReceiveBind` AST
> struct has fields `{patterns, source, remainder, free_count}` — **no guard
> field** — and `halts`/`safe` are external relations that are not Rholang-computable.
> A sound generated-AST lowering of the guarded receive is therefore *impossible*;
> the only sound disposition for the channel/join surfaces is `RhoNativeJoin`,
> enforced by a host join. This is *derived-required*, exactly as
> [08 §3.3](08-runtime-comm-enforcement.md) describes.

## 3. The fail-closed flip gate

With every obligation covered by a compatible disposition and no `Unknown` quality,
`plan_rho_default_backend` admits GuardedRho on the Rho backend
([07 §5](07-language-to-rholang-integration.md)). The test exercises both directions
of the gate:

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
>   if not is_funded(Δ, Σ, margin):  return rest    ▷ OSLF resource axis (08)
>   return commit                                   ▷ consume input, spawn p[σ]
> ```

The substrate's EBA is **not** re-evaluated here — it already classified the
obligation at compile time. The native join handler consults the external relation
(the same `safe`/`halts` the `logic { }` block declared), and RSpace enforces guard
atomicity: a failed guard leaves the message resting, a later satisfying message
still commits.

That run-time behavior is verified directly by `rho_guard_oracle.rs` against the
live f1r3node `RhoRuntime`, using the `where`-guard form to validate the same
"rest, then commit" semantics the native join must reproduce:

| Oracle test | Observation |
|---|---|
| `false_single_bind_guard_leaves_data_and_emits_no_output` | a failed guard emits no body; the rejected datum stays readable |
| `guard_filters_multiple_messages_without_consuming_failed_candidate` | a later satisfying datum fires; the earlier failing datum remains |
| `false_cross_bind_guard_leaves_all_join_inputs` | a failed join guard consumes no input |
| `cross_bind_guard_can_commit_later_without_consuming_failed_pair` | the later satisfying pair commits; the earlier failing input remains |

## 5. The end-to-end picture

Reading the trace as the suite's left-to-right spine:

`?guard:Guard + channels{} + logic{halts,safe}  →  4 obligations  →  {RhoNativeJoin ×2, EffectiveBooleanAlgebra ×2}  →  qualities {RuntimeObservation ×2, RejectSafeApprox ×2}  →  fail-closed flip gate PASSES (no Unknown)  →  host-routed native join enforces the guard at COMM time (algebra never re-run)`

GuardedRho is the proof, in one language, of the suite's two crux claims:

1. **The substrate classifies; the host enforces.** The EBA decided coverage and
   quality at compile time; at run time a native join — not generated Rholang and
   not the algebra — gates the COMM ([08](08-runtime-comm-enforcement.md)).
2. **The logic axis composes with the resource axis.** The COMM fires iff the guard
   holds *and* the rewrite is funded ([09 — OSLF Composition](09-oslf-composition.md)),
   both checked at the boundary, both proven in the same zero-admission `rho_bridge`
   tree ([10 — Formal Verification](10-formal-verification-and-tests.md)).

For the syntax a future GuardedRho author could use to write richer behavioral
guards — `AG safe(q)`, bounded quantifiers, transducer guards — see the proposed
extensions in [06 — Guard Syntax and Extensions](06-guard-syntax-and-extensions.md).
