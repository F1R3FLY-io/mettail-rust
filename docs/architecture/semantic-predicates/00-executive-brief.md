# Executive Brief

Last updated: 2026-06-23

A one-page orientation to the semantic-predicate substrate for principals. The
detail is in the numbered documents; this page is the decision-level summary.

## What it is

The **semantic-predicate substrate** is the theory-of-guards layer of MeTTaIL. It
represents every guard a `language!` can express — over the shape of data, over its
values, or over the behavior of a process — as an element of an **effective Boolean
algebra (EBA)**, decides and classifies it at **compile time**, and hands the
backend fail-closed coverage evidence. It is built once against an abstract algebra
interface, so the same symbolic automata and transducers serve integers,
characters, processes, bags, and trees alike ([D'Antoni & Veanes, 2017](references.md#dantoni-veanes-2017)).

It is not the parser, the Dovetail rewrite engine, or the Rho backend. It owns the
decision *which guarded rewrites and communications a generated language may
perform*, and the evidence that the decision is sound.

## The layer map

| Layer | Owner | Artifact |
|---|---|---|
| guard declaration | `language!` macro | `guards { }`, `?guard:Guard`, `logic { }` |
| predicate algebra | the `prattail` substrate | EBA / SFA / SFT / the algebra tower |
| classification | `rholang-codegen` | obligation · disposition · quality |
| admission | the flip gate | fail-closed `Coverage ∧ ArtifactValidation ∧ NoNewDeadlocks` |
| run-time enforcement | the host (RSpace / native join) | structural match · `where` · `RhoNativeJoin` |

## The two facts a principal must carry

1. **The substrate is classify-only.** It runs at compile time and emits *evidence
   and a quality grade* per guard obligation. It never emits an EBA, SFA, or SFT
   into generated Rholang. At run time the *surviving* guard is enforced by the
   host — by RSpace structural matching, a Rholang `where` boolean guard, or a
   host-routed native join — and the algebra is never re-run. This is why "how does
   Rholang apply the semantic predicate at run time" has the answer *it doesn't
   apply the algebra at all*. See [08 — Runtime COMM Enforcement](08-runtime-comm-enforcement.md).

2. **It composes with OSLF, it is not OSLF.** The predicate algebra is the *logic
   axis* (is the COMM enabled?); OSLF funding is the *resource axis* (is the rewrite
   affordable?). A guarded COMM fires iff `guard-satisfied ∧ funded`. The two are
   distinct effective theories that share a fail-closed, tier-decidable,
   evidence-carrying design — which is exactly why they compose cleanly. See
   [09 — OSLF Composition](09-oslf-composition.md).

## Why this design

- **Soundness is a type, not a convention.** Structural predicates are classical
  and decided exactly; behavioral predicates are only semi-decidable, so their
  complement is unsound to treat classically. The **algebra tower** encodes that
  difference at compile time: a semi-decidable algebra simply lacks the classical
  operations, so no algorithm that needs them can be instantiated over it
  ([05 — Algebra Pyramid](05-algebra-pyramid-and-decidability.md)).
- **Admission is fail-closed.** A language adopts the Rho backend only when every
  guard obligation is covered by a compatible disposition with non-`Unknown`
  quality. Absent evidence, the gate refuses rather than guessing
  ([07 — Language-to-Rholang Integration](07-language-to-rholang-integration.md)).
- **Every claim is mechanized.** The EBA laws, the closure family, the transducer
  algebra, the tier lattice, the mixed-negation soundness, and the guarded-COMM
  bridge are zero-admission Rocq theories ([10 — Formal Verification](10-formal-verification-and-tests.md)).

## What can be written today, and what is proposed

Of the algebra families implemented and largely proved in `prattail`, only relation
queries, the propositional connectives, prefix-call quantifiers, and integer
comparisons are reachable from `language!` source today. Everything
modal/temporal, transducer-shaped, tree/collection/product-shaped, and every
effective-theory literal beyond integer comparison is *algebra without surface
syntax* — built, and for several now wired into the live pipeline as a default-off
lint, but unreachable from `language!` source.
[06 — Guard Syntax and Extensions](06-guard-syntax-and-extensions.md) documents
exactly what is supported and proposes a clean syntax to close the gap, with a
sharp `✅ supported / ◐ partial / ⊳ proposed` distinction.

## The principal's takeaways

- The substrate makes guard soundness a *compile-time, fail-closed, mechanically
  verified* property; run-time cost stays bounded because the host enforces a
  pre-classified decision, never the algebra.
- A behavioral guard is *reject-safe*: it may reject a satisfiable case but never
  fires falsely — the conservative posture that keeps a semi-decidable predicate
  sound in a concurrent setting.
- The framework already covers every data type by construction; the open work is
  *surface syntax*, not algebra — the algebras are built and several are already wired
  into the live pipeline as default-off lints, so what remains is a `language!`
  spelling, scoped and proposed in [06](06-guard-syntax-and-extensions.md).
