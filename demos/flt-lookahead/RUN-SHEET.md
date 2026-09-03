# Lookahead — λ-calculus computed by the Rholang machine, filtered, and destructured

## The claim, in one sentence

> Classic λ-calculus programs are embedded in Rholang, **speculatively evaluated by the Rholang
> machine** one enumerated communication at a time, and the results are then separated by shape
> and selected by a predicate — with the surviving term destructured back out into Rholang.

Nothing in these programs spells an answer. Every value that appears arrives because the machine
computed it.

> Status: **VALIDATED end to end, 2026-07-26; RE-VALIDATED 2026-07-28.** Every command below was
> run three times against a freshly built binary; output was byte-identical on every run.
>
> ★ **The 2026-07-28 re-validation was a differential, not a re-read.** Twenty-one defects closed
> that day across two repositories. All four beats were run against a binary built **before** any
> of them and one built **after**, and every transcript — including beat 4's trace digest
> `0x4f13e762…`, which is the field that is supposed to be a function of the program alone — was
> byte-identical modulo the binary's own name line. The four changes with a plausible route to
> this page were the guard-substrate residual-binder fix (`69c66cd1`), the `@`-sigil display fix
> (`5a5cc9b0`), the binder-congruence float-arm restriction (`359220f3`), and the
> operator-precedence overhaul (`3ff1c98b`…`ce887d0b`); none of the four moved a byte here. The
> precedence work in particular cannot: a census over every `.rho` file in `demos/` finds exactly
> one arithmetic expression in the whole corpus, and it is in `flt-church-desk`, not here.

## Setup — before the audience arrives

```
cargo build -p rholang-runtime --bin rholang --features "rholang-runtime lambda-runtime calculator-runtime"
```

**No stack incantation.** This page used to open with `export RUST_MIN_STACK=134217728`, attributed
to "λ terms of this size exceed the default thread stack". That was wrong twice, and both halves
were settled by measurement: the interpreter's parse and lowering run in `#[tokio::main]`'s
`block_on` body — on the **main** thread, whose size that variable does not set — and every
committed demo in this directory was measured running green with the variable unset entirely.
`no_run_sheet_command_line_raises_the_stack` now asserts its absence, so the incantation cannot
come back as folklore. Run everything from the workspace root; each command completes in well
under a second.

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
$ target/debug/rholang demos/flt-lookahead/01-computed-desk.rho
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
$ target/debug/rholang demos/flt-lookahead/02-the-desk.rho
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
for(@lambda:Term`lam f. lam x. (f, ${rest})` <- @"results") { … }
```

requires the body to be an *application of the outer binder* — true of every numeral ≥ 1, false of
every boolean. **The booleans are refused structurally and left resting on `@"results"`.**

That is pattern-matching *into* a foreign language: `rest` is now a Rholang value holding a
sub-term of a λ-term.

---

## Beat 3 — selected by predicate (2 min)

```
$ target/debug/rholang demos/flt-lookahead/03-predicate.rho
```
```
  @"OUT" observations (2):
    [0] ⟦λ.λ.0⟧
    [1] ⟦λ.λ.0⟧
  lookahead: 4 request(s) served · ^spec-success: 3 · ^spec-failure: 0 · ^spec-truncated: 0
```

The **same four programs, the same pool** — and a different question. Here the pattern binds the
whole computed term and a `where` clause decides:

```
for(@lambda:Term`${r}` <- @"results" where lambda:Term`${r}` == lambda:Term`lam t. lam f. f`) { @"OUT"!(r) }
```

`⟦λ.λ.0⟧` is FALSE. The predicate accepted the one boolean it asked for and refused both numerals
*and* the other boolean. The three refused results are still resting.

### …and the same answer collected a second way

**Two observations, one value.** A served `[*]` publishes each branch twice — the bare term on the
reply channel, and a provenance pair `[trace, [term…]]` on `@"^spec-success"` — so this beat asks
the *same* predicate on the *other* channel and republishes what it finds:

```
for(@[trace, [term]] <- @"^spec-success" where term == lambda:Term`lam t. lam f. f`) {
  @"OUT"!(trace.concat([term]).nth(trace.concat([term]).length() - 1))
}
```

The body rebuilds the FIPS `success` **entry** from the wire pair — the FIPS's rule is that an
extra list is *concatenated to the end of the trace* — and reads its leaf as the last element.
That value travels through a list construction, a concatenation, a length and an index, and still
lands on the term the reply channel delivered directly. The equality is decided by the substrate,
not by the eye: routing both through a join and publishing `a == b` prints `⟦true⟧`.

**Point at `^spec-success: 3`.** The other three beats report every branch they published; this one
reports one fewer than the four it served, because the counter is *what is still resting* and this
beat consumed one. Rholang has no peek — `<-` and `<=` are the only arrows — so reading provenance
necessarily consumes it.

⚠ `@"^spec-success"` is **one channel for the whole run**, not a per-request channel. It carries no
field naming the reply channel a request answered on, so the correspondence with `@"results"` holds
here only because every `[*]` in the file targets `@"results"`.

**Beats 2 and 3 together are the argument.** Same computed pool; one selects by structure and gets
a numeral, the other selects by predicate and gets a boolean. A filter that admitted everything, or
one the substrate could not decide, would answer both the same way.

---

## Beat 4 — the honest limit (2 min)

```
$ target/debug/rholang demos/flt-lookahead/04-divergence.rho
```
```
  @"OUT" observations (1):
    [0] ⟦(1 (1 (1 (1 (1 0)))))⟧
  lookahead: 2 request(s) served · ^spec-success: 2 · ^spec-failure: 1 · ^spec-truncated: 0
    ^spec-failure[0] trace 0x4f13e762…  code 8 (guest evaluator: out of fuel)  the guest evaluator
      rested on ^drive-fuel:mettail-langdef-v1:6ef0c40636bb0bca: the stuck redex is
      ⟦App(λ.App(0, 0), λ.App(0, 0))⟧
```

Beats 1–3 all end with an answer, which is the easy half of the claim: a machine that only ever
reports success is indistinguishable from one that reports success unconditionally. This beat runs
`plus 2 3` and **Ω** — `(λx. x x)(λx. x x)`, which β-reduces to itself forever — in the same
program.

**Point at the two counters.** `^spec-success: 2` and `^spec-failure: 1` — Ω's branch is in *both*,
and that is the design, not a bookkeeping accident. Its branch really does reach tuplespace
quiescence (`E(S)` empties, nothing raises) while the guest's own evaluator computed nothing along
it. Those are two different facts. Collapsing them would make "no answer exists" and "I gave up"
indistinguishable, which is the silence the whole fail-closed design exists to prevent.

The message names the term in the **machine's neutral notation** — `App(…)` for λ's own
constructor, `λ.` and de-Bruijn indices for the reserved reflected-ABI tags. `flt-church-desk`'s
`divergence.rho` prints the guest's *surface* syntax instead, and the difference is deliberate: a
`^spec-failure` entry is data on the tuplespace, which a guest-independent reader has to parse; the
interpreter holds the `Par` and may sugar it.

**The trace digest is quotable, and getting there found two defects.** Building this beat is what
made them visible: the digest used to differ on *every run*, and before the `^spec-failure`
renderer landed it was buried inside a prost `Debug` dump nobody read.

Two independent non-content inputs were reaching it. The interpreter seeded its injection
randomness from OS entropy — `Blake2b512Random::create_from_length(128)` reads like a fixed-width
seed but fills its buffer with `thread_rng()` — and `step_digest` folded the **store index**, which
is not content at all but a local address assigned by task-arrival order, since `HotStore` prepends
and every branch of a `|` is a detached `tokio::spawn`. The second is why a dose-response curve
over `TOKIO_WORKER_THREADS` was the discriminator that cracked it: 1 thread gave one digest, 2 gave
two, 32 gave twenty-of-twenty.

Both are closed. The digest above is now invariant across processes **and** across scheduler
widths (1, 2, 8, 32 worker threads all agree), and the whole transcript is asserted byte-for-byte.

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

## Files

| | |
|---|---|
| `01-computed-desk.rho` | two programs, computed, destructured |
| `02-the-desk.rho` | four programs, separated by shape |
| `03-predicate.rho` | the same four, selected by predicate |
| `04-divergence.rho` | one that finishes and one that cannot, in the same run |
