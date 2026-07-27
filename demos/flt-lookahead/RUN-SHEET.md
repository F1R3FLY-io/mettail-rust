# Lookahead — λ-calculus computed by the Rholang machine, filtered, and destructured

## The claim, in one sentence

> Classic λ-calculus programs are embedded in Rholang, **speculatively evaluated by the Rholang
> machine** one enumerated communication at a time, and the results are then separated by shape
> and selected by a predicate — with the surviving term destructured back out into Rholang.

Nothing in these programs spells an answer. Every value that appears arrives because the machine
computed it.

> Status: **VALIDATED end to end, 2026-07-26.** Every command below was run three times against a
> freshly built binary; output was byte-identical on every run.

## Setup — before the audience arrives

```
cargo build -p rholang-runtime --bin rhocalc --features "rhocalc-runtime lambda-runtime calculator-runtime"
export RUST_MIN_STACK=134217728
```

The stack setting is required: λ terms of this size exceed the default thread stack. That is a
separately-tracked defect with its own root-cause plan — it is not a property of the feature being
shown. Run everything from the workspace root; each command completes in well under a second.

## The operator

```
x!(P)[*]   ≡   explore every execution path of P, deliver each path's terminal term to x
```

`[*]` lowers to a **request**, not a send — the subject is never deposited on the channel. An
installed system process consumes the request, funds a fresh speculative tuplespace from this
deploy's phlogiston, injects the λ guest's own installed Rho-net program alongside a seed, and
enumerates every enabled rendezvous breadth-first until each branch reaches quiescence. Only
computed terminal terms ever rest on the channel.

If the engine were missing, the request would **rest** and the interpreter would say so. It cannot
quietly publish nothing, and it cannot publish the subject back as an "answer".

---

## Beat 1 — the machine computes (1 min)

```
$ target/debug/rhocalc demos/flt-lookahead/01-computed-desk.rho
```
```
mode: process → running to rest on the f1r3node reducer (observing @"OUT")
  @"OUT" observations (1):
    [0] ⟦(1 (1 (1 (1 (1 0)))))⟧
  lookahead: 2 request(s) served · ^spec-success: 2 · ^spec-failure: 0 · ^spec-truncated: 0
```

Two λ programs — `plus 2 3` and `mult 2 3` — each speculated. **Point at `2 request(s) served`.**
The output is the *body* of a computed Church numeral: five nested applications, extracted by a
receive pattern that reached inside the foreign term.

`cat` the file. There is no numeral in it.

---

## Beat 2 — separated by shape (2 min — the point)

```
$ target/debug/rhocalc demos/flt-lookahead/02-the-desk.rho
```
```
  @"OUT" observations (1):
    [0] ⟦(1 (1 (1 (1 0))))⟧
  lookahead: 4 request(s) served · ^spec-success: 4 · ^spec-failure: 0 · ^spec-truncated: 0
```

Now **four** programs — two Church numerals and two Church booleans:

| program | reduces to | body is |
|---|---|---|
| `plus 2 3` | Church 5 | an **application** |
| `mult 2 3` | Church 6 | an **application** |
| `not true` | FALSE | a **variable** |
| `and true true` | TRUE | a **variable** |

Church numerals and Church booleans are **both two-binder terms**, so counting binders cannot tell
them apart. The pattern

```
for(@lambda`lam f. lam x. (f, ${rest})` <- @"results") { … }
```

requires the body to be an *application of the outer binder* — true of every numeral ≥ 1, false of
every boolean. **The booleans are refused structurally and left resting on `@"results"`.**

That is pattern-matching *into* a foreign language: `rest` is now a RhoCalc value holding a
sub-term of a λ-term.

---

## Beat 3 — selected by predicate (2 min)

```
$ target/debug/rhocalc demos/flt-lookahead/03-predicate.rho
```
```
  @"OUT" observations (1):
    [0] ⟦λ.λ.0⟧
  lookahead: 4 request(s) served · ^spec-success: 4 · ^spec-failure: 0 · ^spec-truncated: 0
```

The **same four programs, the same pool** — and a different question. Here the pattern binds the
whole computed term and a `where` clause decides:

```
for(@lambda`${r}` <- @"results" where lambda`${r}` == lambda`lam t. lam f. f`) { … }
```

`⟦λ.λ.0⟧` is FALSE. The predicate accepted the one boolean it asked for and refused both numerals
*and* the other boolean. The three refused results are still resting.

**Beats 2 and 3 together are the argument.** Same computed pool; one selects by structure and gets
a numeral, the other selects by predicate and gets a boolean. A filter that admitted everything, or
one the substrate could not decide, would answer both the same way.

---

## What this rests on

- **The results are computed.** No numeral or boolean literal appears in any of these files.
  Beat 1's success trace is 403 enumerated communications.
- **The refused results rest.** They are not consumed and not destroyed.
- **`[*]` genuinely enumerates.** It routes through the branching engine, not the single-path
  driver — there is a test asserting the single-path seed is *absent* from the lowering, because
  λ's confluence would make that shortcut invisible in its own output.
- **Determinism.** All three commands, three runs, freshly built binary, byte-identical.

## Scope — what this does not show

λ-calculus is **confluent**, so every path of a λ program reaches the same normal form and each
success set here is a singleton. That is mathematics, not a limit of the engine: on a non-confluent
guest it returns several results, gated by a send/receive race yielding two leaves, with a
teeth-test proving two *independent* communications yield one.

The `failure` map is populated correctly for a divergent subject — Ω reports on `^spec-failure` —
but its message currently embeds a raw internal dump, so that beat is held back. See
`demos/flt-church-desk/divergence.rho` for a clean divergence beat.

## Files

| | |
|---|---|
| `01-computed-desk.rho` | two programs, computed, destructured |
| `02-the-desk.rho` | four programs, separated by shape |
| `03-predicate.rho` | the same four, selected by predicate |
