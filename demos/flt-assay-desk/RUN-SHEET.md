# The Foreign Assay Desk — foreign terms reduced by the Rholang machine, then filtered by a `where` guard

A live demonstration of Rholang's **Foreign Language Term** (FLT) integration, end to end, on
F1r3node's Rho machine. A guest language — the untyped $`\lambda`$-calculus — is embedded in
Rholang source; its terms are **driven to normal form by the Rholang machine itself**, not by a
host interpreter; the results are **extracted** into the Rholang program by typed-hole patterns;
and a **`where` clause selects** the ones the program needs, leaving the rest resting on the
channel.

Everything below is stock Rholang plus the bundled `lambda` guest. There is no Rust harness in the
demo path: the presenter runs one interpreter binary on seven committed `.rho` files.

> Status: **VALIDATED end to end, 2026-07-26** — every command on this page was run and every
> output is the observed one, pinned. Every file produced byte-identical output on every run:
> six consecutive full passes over the first six files, then three more over all seven.
> The whole script is a CI gate: `rholang-runtime/tests/assay_desk_demo.rs` drives the built
> `rholang` binary with these exact command lines and asserts each beat's observable, plus a
> runtime-level readback for the "…and the refused results are still on the book" half that the
> interpreter's single-channel `@"OUT"` view cannot show. A command line added or respelled here
> without matching coverage there fails the build
> (`every_run_sheet_command_line_is_driven_by_this_test`), and every transcript printed below is
> compared against a live run (`every_transcript_in_the_run_sheet_is_the_observed_output`).

---

## The claim, in one sentence

> A foreign language is embedded in Rholang; its terms are reduced to normal form by the Rholang
> machine, one committed COMM at a time; and the results are then filtered by a predicate the
> substrate decides — keeping some and refusing others, with the refused ones left untouched.

## The shape

```
       ╭──────────────── written in the GUEST's own syntax ────────────────╮
       │                                                                   │
  contract-a.rho    lambda`((lam a. lam b. a, lam x. x), lam a. lam b. a)`    │  ⎫
  contract-b.rho    lambda`((lam a. lam b. b, lam x. x), lam a. lam b. b)`    │  ⎬ Beats 1–2
  contract-c.rho    lambda`(lam x. x, lam a. lam b. a)`                       │  ⎭
       │                                                                   │
       ╰───────────────────────────────┬───────────────────────────────────╯
                                       │
                       reflected into the guest's own
                       in-Rho reduction engine and
                       β-driven to QUIESCENCE on the
                       f1r3node reducer  (^drive)
                                       │
                                       ▼
             ⟦λ.0⟧              ⟦λ.λ.0⟧             ⟦λ.λ.1⟧
          the identity        the mirror          the constant
               I                   C                   K
                                       │
                                       │  published as three resting data
                                       ▼
                            ┌──────────────────────┐
                            │      @"assay"        │   ⎫
                            └──────────┬───────────┘   ⎪
                                       │               ⎪
     for( @lambda`${r}` <- @"assay"  where lambda`${r}` == … )⎬ Beats 3–5
             └──── EXTRACT ────┘  └──── FILTER ────┘   ⎪
                                       │               ⎭
                        ┌──────────────┴──────────────┐
                        ▼                             ▼
                   @"OUT"                        still on @"assay"
              the one accepted result        the refused results, untouched
```

Two mechanisms are stacked in that one receive, and they do different jobs:

| | what it is | what it does |
|---|---|---|
| `` @lambda`${r}` `` | the receive **pattern** — itself an FLT, carrying one typed hole | matches a reflected guest term by **shape** and binds the whole $`\lambda`$-term to `r`. This is the **extraction**: the foreign result becomes a value the Rholang program holds. A `${x}` hole is a secure typed-AST hole; it never splices strings (No-Injection). |
| `` where lambda`${r}` == … `` | the **guard** | re-quotes the captured term and **decides** it against a reference term. This is the **filter**, and the decision is made by the substrate, not by the pattern. |

---

## Setup (do this before the audience arrives)

```
$ cargo build -p rholang-runtime --bin rholang --features "rholang-runtime lambda-runtime calculator-runtime"
```

Both features are required by the `rholang` bin target: `rholang-runtime` pulls in the generated
Rholang language and its AST-first lowering, `lambda-runtime` pulls in the production
`LambdaLanguage` that the interpreter registers as the `lambda` guest. The build takes several
minutes cold. Everything after this is instant.

CI drives the same binary through `env!("CARGO_BIN_EXE_rholang")`, so the presenter's binary and
the gated one are built from one source. A `--release` build behaves identically, but it lands at
`target/release/rholang`, so the command lines below would need that path instead — the debug
binary is what this page is written against, and every run of it completes in well under a second.

Run every command from the workspace root.

---

## Beat 1 — A foreign language, inside Rholang, reduced by Rholang (2 min)

**Show the term as written.** This is the hook: it is not Rholang, and it is not quoted text.

```
$ tail -1 demos/flt-assay-desk/contract-a.rho
```

```
lambda`((lam a. lam b. a, lam x. x), lam a. lam b. a)`
```

> "`` lambda`…` `` is Rholang's opener for a term of another language. Everything between the
> back-ticks is the **guest's** concrete syntax — the untyped λ-calculus — handed to the guest's
> own reflector. In the guest, `(f, a)` is application. So with the two standard combinators
>
>     K = lam a. lam b. a     the CONSTANT combinator — keep the first argument
>     I = lam x. x            the IDENTITY combinator
>
> that line is the redex `(K I) K`."

**Now run it.**

```
$ target/debug/rholang demos/flt-assay-desk/contract-a.rho
```

```
rholang — Rholang (Rholang 1.4) interpreter
source: demos/flt-assay-desk/contract-a.rho
comments: 36 retained on the COMMENTS channel
mode: term → reducing to normal form on the f1r3node reducer
  normal form on @"OUT" (1):
    [0] ⟦λ.0⟧
  ^fired ledger: ["Beta", "Beta"]   (2 in-Rho rewrite firing(s))
  ^drive-err: 0 datum(a) · ^drive-fuel: 0 datum(a)   (both empty ⟹ terminated by quiescence)
```

**Point at, in this order:**

1. `mode: term` — the program is a bare foreign term, so the interpreter *evaluates* it: it seeds
   the reflected term into the guest's own in-Rho reduction engine and lets it run.
2. `⟦λ.0⟧` — the normal form, in de Bruijn form: $`\lambda.0`$ is `lam x. x`, the identity.
   `(K I) K` $`\longrightarrow_\beta (\lambda b.\,I)\,K \longrightarrow_\beta I`$ — K kept its
   first argument and discarded its second.
3. **`^fired ledger: ["Beta", "Beta"]`** — this is the machine's own receipt. Two β steps fired,
   and they fired *as communications on RSpace*. The host did not reduce this term; it was
   reduced by the same reducer that runs every other Rholang program.
4. `^drive-err: 0 · ^drive-fuel: 0` — it stopped because it reached a **normal form**, not
   because it ran out of fuel and not because the driver met a head it could not recognize.
   Both channels empty is the interpreter's proof of quiescence.

> "That is the whole claim in one screen. A different language, written in its own syntax, living
> inside a Rholang program, and evaluated by the Rholang machine."

---

## Beat 2 — Two more terms, two more answers (1 min)

```
$ target/debug/rholang demos/flt-assay-desk/contract-b.rho
```

```
rholang — Rholang (Rholang 1.4) interpreter
source: demos/flt-assay-desk/contract-b.rho
comments: 25 retained on the COMMENTS channel
mode: term → reducing to normal form on the f1r3node reducer
  normal form on @"OUT" (1):
    [0] ⟦λ.λ.0⟧
  ^fired ledger: ["Beta", "Beta"]   (2 in-Rho rewrite firing(s))
  ^drive-err: 0 datum(a) · ^drive-fuel: 0 datum(a)   (both empty ⟹ terminated by quiescence)
```

Contract B is `(C I) C` where `C = lam a. lam b. b` keeps its **second** argument — the mirror
image of Contract A, the same two β steps, a different answer: $`\lambda.\lambda.0`$.

```
$ target/debug/rholang demos/flt-assay-desk/contract-c.rho
```

```
rholang — Rholang (Rholang 1.4) interpreter
source: demos/flt-assay-desk/contract-c.rho
comments: 27 retained on the COMMENTS channel
mode: term → reducing to normal form on the f1r3node reducer
  normal form on @"OUT" (1):
    [0] ⟦λ.λ.1⟧
  ^fired ledger: ["Beta"]   (1 in-Rho rewrite firing(s))
  ^drive-err: 0 datum(a) · ^drive-fuel: 0 datum(a)   (both empty ⟹ terminated by quiescence)
```

**Point at:** one firing this time, and — this is the part that matters for the next beat —
Contract C *arrives* as `(lam x. x, lam a. lam b. a)`, an **application**. It is not the constant
combinator. It only *becomes* the constant combinator $`\lambda.\lambda.1`$ after the machine
reduces it.

Three contracts, three distinct results:

| contract | as written | normal form | β firings |
|---|---|---|---|
| A | `((lam a. lam b. a, lam x. x), lam a. lam b. a)` | `⟦λ.0⟧` — the identity `I` | 2 |
| B | `((lam a. lam b. b, lam x. x), lam a. lam b. b)` | `⟦λ.λ.0⟧` — the mirror `C` | 2 |
| C | `(lam x. x, lam a. lam b. a)` | `⟦λ.λ.1⟧` — the constant `K` | 1 |

---

## Beat 3 — The desk: three results rest, a `where` guard picks one (3 min — THE POINT)

**Show the program.** It is seven lines.

```
$ tail -7 demos/flt-assay-desk/desk-accepts-constant.rho
```

```
@"assay"!(lambda`lam x. x`) |
@"assay"!(lambda`lam a. lam b. b`) |
@"assay"!(lambda`lam a. lam b. a`) |

for(@lambda`${r}` <- @"assay" where lambda`${r}` == lambda`lam a. lam b. a`) {
  @"OUT"!(lambda`${r}`)
}
```

> "Three sends and one receive. The three payloads are the three normal forms we just watched the
> machine compute — the identity, the mirror, the constant. They are resting on one channel.
>
> The receive does two things at once. Its **pattern** is itself a foreign term with a typed hole
> in it, `` @lambda`${r}` ``; that matches a reflected guest term by shape and binds it — that is how the
> foreign result gets *into* the Rholang program. Its **`where` clause** is the filter: it decides
> the captured term against the constant combinator.
>
> Three data are resting and exactly one satisfies the guard. So the receive has to *search*."

**Now run it.**

```
$ target/debug/rholang demos/flt-assay-desk/desk-accepts-constant.rho
```

```
rholang — Rholang (Rholang 1.4) interpreter
source: demos/flt-assay-desk/desk-accepts-constant.rho
comments: 53 retained on the COMMENTS channel
mode: process → running to rest on the f1r3node reducer (observing @"OUT")
  @"OUT" observations (1):
    [0] ⟦λ.λ.1⟧
```

**Point at:** `⟦λ.λ.1⟧` — Contract C's result, and *only* that one. `⟦λ.0⟧` and `⟦λ.λ.0⟧` were
offered to the same receive and refused. They are not consumed, not destroyed: they are still
resting on `@"assay"` when the program comes to rest. (See
[What rests](#what-rests--the-half-the-terminal-cannot-show), and Beat 4, which shows one of them
still being there.)

> ⚠ **This beat did not work this morning.** Until 2026-07-26 a guarded receive tested one
> candidate and, on rejection, gave up — it never went on to the next resting datum (defect D1,
> repaired in `f1r3node-rust-mettail` `feature/mettail` by `6bc58743` and `5d37f67e`;
> `SpaceMatcher::extract_guarded_data_candidates` is now one depth-first search with the guard
> evaluated at the leaf, returning the lexicographically least satisfying selection). A three-
> candidate filter with the admissible one *last* is exactly the case that used to strand. Mention
> it if the audience asks why filtering across several results is worth a beat.

---

## Beat 4 — Change one token; the same set yields a different result (1.5 min)

`desk-accepts-identity.rho` is the previous file with **one changed term**: what the `where`
clause compares against. Same three data, same channel, same receive pattern.

```
$ target/debug/rholang demos/flt-assay-desk/desk-accepts-identity.rho
```

```
rholang — Rholang (Rholang 1.4) interpreter
source: demos/flt-assay-desk/desk-accepts-identity.rho
comments: 24 retained on the COMMENTS channel
mode: process → running to rest on the f1r3node reducer (observing @"OUT")
  @"OUT" observations (1):
    [0] ⟦λ.0⟧
```

**Point at:** `⟦λ.0⟧`. Two things follow immediately, and neither is arguable.

1. **The guard is genuinely decided.** A guard the substrate could not decide fails *closed* —
   it would refuse everything and this file would publish nothing. It published.
2. **The identity was resting on `@"assay"` all along**, including during Beat 3. Beat 3
   *selected* out of the resting set; it did not consume it.

Side by side — one unchanged set of results, three predicates, three outcomes:

| file | the guard | kept | left behind on `@"assay"` |
|---|---|---|---|
| `desk-accepts-constant.rho` | `` == lambda`lam a. lam b. a` `` | `⟦λ.λ.1⟧` | `⟦λ.0⟧`, `⟦λ.λ.0⟧` |
| `desk-accepts-identity.rho` | `` == lambda`lam x. x` `` | `⟦λ.0⟧` | `⟦λ.λ.0⟧`, `⟦λ.λ.1⟧` |
| `desk-accepts-nothing.rho` | `` == lambda`lam a. lam b. lam c. a` `` | *nothing* | all three |

---

## Beat 5 — Two ways to be refused, and why each matters (1.5 min — the honesty beat)

### 5a — The reduction is load-bearing

Offer the desk Contract C **as it arrives** instead of as it reduces. Same channel, same pattern,
and a `where` clause that is character-for-character Beat 3's — it still asks for the constant
combinator. Only the datum changed:

| | the datum on `@"assay"` | what it is |
|---|---|---|
| Beat 3 | `` lambda`lam a. lam b. a` `` | Contract C's **normal form** — the constant combinator `K` |
| here | `` lambda`(lam x. x, lam a. lam b. a)` `` | Contract C **as it arrives** — the application `(I K)` |

```
$ target/debug/rholang demos/flt-assay-desk/desk-refuses-the-unreduced-arrival.rho
```

```
rholang — Rholang (Rholang 1.4) interpreter
source: demos/flt-assay-desk/desk-refuses-the-unreduced-arrival.rho
comments: 35 retained on the COMMENTS channel
mode: process → running to rest on the f1r3node reducer (observing @"OUT")
  @"OUT": (the program rested without publishing any observation)
```

> "The desk's predicate is over the **result** of the foreign computation. `(I K)` reduces to `K`
> — but only if something reduces it. So the run-to-completion in Beat 2 was not a warm-up act:
> it is the step that turns an unacceptable arrival into an acceptable result. Take the reduction
> away and the same desk, with the same guard, settles nothing."

This also rules out a whole class of ways the demo could pass for the wrong reason: a guard that
compared **source text**, or that matched loosely on the guest-term envelope rather than on the
term, would have accepted this datum. It did not.

### 5b — And the guard can refuse everything

Back to the three reduced results, same pattern; the guard now names the *three*-argument constant
combinator `lam a. lam b. lam c. a`, which is not the normal form of any contract.

```
$ target/debug/rholang demos/flt-assay-desk/desk-accepts-nothing.rho
```

```
rholang — Rholang (Rholang 1.4) interpreter
source: demos/flt-assay-desk/desk-accepts-nothing.rho
comments: 30 retained on the COMMENTS channel
mode: process → running to rest on the f1r3node reducer (observing @"OUT")
  @"OUT": (the program rested without publishing any observation)
```

The search exhausts, nothing is published, and all three results rest.

> "Three predicates over one unchanged set: one keeps the constant, one keeps the identity, one
> keeps nothing. **No single defect produces all three.** A guard that admitted everything would
> have settled something here. A guard that could not be evaluated — one that failed closed —
> would have settled nothing in the two beats before. And a guard that only ever tested the first
> resting datum could not have returned two *different* answers from one unchanged set. The filter
> is doing exactly what it looks like it is doing."

---

## What rests — the half the terminal cannot show

The interpreter reports one channel, `@"OUT"`. "And the refused results are still on the book" is
a fact about a *second* channel of the *same* quiescent store, so it is asserted at the runtime
level instead, by `rholang-runtime/tests/assay_desk_demo.rs`
(`beat_3_the_two_refused_results_are_still_resting_on_the_book`,
`beat_4_the_constant_combinator_is_among_what_this_desk_leaves_behind`,
`beat_5_a_refusing_guard_consumes_nothing_at_all`,
`beat_5a_the_unreduced_arrival_is_refused_and_left_resting`). Each lowers the committed `.rho`
file through the same parse-and-lower path the interpreter uses, runs it to rest, and reads
`@"assay"` and `@"OUT"` from **one** execution:

| file | `@"OUT"` | resting on `@"assay"` |
|---|---|---|
| `desk-accepts-constant.rho` | the constant combinator | the identity **and** the mirror |
| `desk-accepts-identity.rho` | the identity combinator | the mirror **and the constant** |
| `desk-refuses-the-unreduced-arrival.rho` | *empty* | the un-reduced arrival `(I K)` |
| `desk-accepts-nothing.rho` | *empty* | all three |

Read the middle row against the top one: what Beat 3 accepted is exactly what Beat 4 leaves
behind, and vice versa. Neither desk consumed what its guard refused, and neither fabricated a
value.

Those expectations are never hard-coded as a rendering of a reflected $`\lambda`$-term. Each is
minted by `resting_display_of`, which publishes that one guest term **with no receiver at all**
and reads back what rests — so the expected value comes from the same reflection path as the value
under test, and a change to the reflected wire format can neither make the test pass vacuously nor
fail spuriously.

---

## Why this demo cannot pass vacuously

| failure mode it would be | what would be observed | which beat rules it out |
|---|---|---|
| the FLT is inert — never reduced, only echoed | Beat 1 would print the un-reduced application and an empty `^fired` ledger | Beat 1: `^fired ["Beta","Beta"]`, and Beat 2's Contract C, whose *input* is not a $`\lambda`$ at all |
| the drive ran out of fuel and the "normal form" is a stuck term | `^drive-fuel` would carry the stuck redex | Beats 1–2: `^drive-err: 0 · ^drive-fuel: 0` |
| the `where` guard admits everything | Beat 5b would settle something | Beat 5b |
| the `where` guard cannot be decided and fails closed | Beats 3 and 4 would settle nothing | Beats 3, 4 |
| the guard tests only the first resting datum | one fixed answer regardless of predicate | Beats 3 vs 4 — two different answers, one unchanged set |
| the guard compares source text, or matches the guest-term envelope rather than the term | the un-reduced arrival would be accepted by a predicate naming its normal form | Beat 5a |
| the reduction is decorative — the desk would accept the arrival either way | Beat 5a would settle the constant combinator | Beat 5a |
| the receive consumed everything and published one | `@"assay"` would be empty afterwards | the runtime readback above |
| the sheet drifted from what runs | — | `every_run_sheet_command_line_is_driven_by_this_test`, and `every_transcript_in_the_run_sheet_is_the_observed_output`, which runs every command on this page and compares its output to the block printed beneath it |
| a lucky schedule | — | `every_demo_file_is_byte_identical_over_consecutive_runs`; six full passes by hand |

---

## What the speculation half will add when `[*]` lands

The user asked for the several filtered results to come from **both** (a) several foreign terms,
each driven to completion, and (b) several paths through **one** foreign term explored by `[*]`
lookahead speculation. **This demo is (a).** (b) needs the `[*]` space fork, which is in flight
and not on this branch, so nothing here depends on it.

The demo is shaped so (b) is **additive**: the desk reads `@"assay"` and has no interest in who
published there. When `[*]` lands it adds beats *before* Beat 3 and changes nothing after it —

* **one** contract containing a `[*]` lookahead, whose speculation forks the space into several
  candidate continuations;
* each fork driven to rest by the same `^drive` quiescence driver, and each fork's normal form
  published on `@"assay"` — the same channel, the same shape of datum;
* Beats 3, 4 and 5 then run **unchanged**, filtering across the forks' results instead of across
  three files' results.

The `.rho` files that would change are the contract files only. `desk-accepts-*.rho`, their
expected outputs, and their tests are agnostic to the provenance of the resting data.

---

## Scope notes — what this demo does *not* do, and why

* **The three payloads on `@"assay"` are the normal forms, written out.** They are not piped from
  Beats 1–2 at run time, because a foreign term embedded inside a *process* is currently **inert**:
  the interpreter's process mode runs the program to rest but installs no guest backend and seeds
  no drive, so an FLT in a send stays un-β-reduced (`demos/flt-foreign-exchange/foreign-exchange.rho`
  demonstrates exactly that — it publishes the un-reduced `⟦(λ.0 λ.λ.1)⟧`). Only a *bare term*
  program takes the drive path. The three contract files are therefore separate programs, and the
  correspondence between what they produce and what the desk filters is **machine-checked, not
  assumed**: `each_desk_payload_is_the_normal_form_its_contract_reduced_to` runs each of the desk's
  three payloads as a bare term through the same interpreter and requires (i) that it reduces to
  the same normal form the corresponding contract reduced to, and (ii) that its `^fired` ledger is
  **empty** — which is the reducer's own statement that the payload is *already* in normal form.
  `the_desk_files_publish_exactly_those_three_payloads` ties those probe terms to the sends the
  committed desk files actually make. Driving an FLT *inside* a process
  needs a change to the interpreter's process mode (install the guest backend, seed a drive per
  FLT); that is a production change, deliberately not made here.
* **No collection operations.** Nothing in this demo builds a list, map or PathMap of results and
  filters the collection. Results are separate resting data and the filter is a guarded receive —
  which is both the shape that works today and the sharper demonstration, since the guarded search
  over resting data is the mechanism that was repaired this morning.
* **No labels on `@"OUT"` — one datum per accept, deliberately.** An earlier draft had each accept
  publish the result *and* a human-readable label, `` @"OUT"!(lambda`${r}`) | @"OUT"!("ACCEPTED: …") ``.
  That is two data resting on one channel, and they come back in an order the scheduler decides:
  nine sequential hand-runs all put the term first, and the first run under parallel load swapped
  them. The demo's own determinism gate
  (`every_demo_file_is_byte_identical_over_consecutive_runs`) caught it, and the label was cut
  rather than hoped over — a run sheet promising one ordering and a live run printing the other is
  the one failure that cannot be recovered from in front of an audience. **One observation per
  channel cannot be misordered.** (Folding the label into a single datum was the other option and
  is worse: a list payload `["ACCEPTED", …]` renders its reflected element structure raw, and a
  polyadic send whose payload includes an FLT does not lower at all today — it fails closed with
  `unknown guest language ⌜lam⌝`.) The labelling therefore lives in this page and in each file's
  header comment, where it belongs.

---

## Files

| file | what it is |
|---|---|
| `contract-a.rho` | bare FLT `(K I) K` — drives to `⟦λ.0⟧` in 2 β firings |
| `contract-b.rho` | bare FLT `(C I) C` — drives to `⟦λ.λ.0⟧` in 2 β firings |
| `contract-c.rho` | bare FLT `I K` — drives to `⟦λ.λ.1⟧` in 1 β firing |
| `desk-accepts-constant.rho` | three results rest; the guard keeps the constant combinator |
| `desk-accepts-identity.rho` | the same three; one changed token in the guard keeps the identity |
| `desk-refuses-the-unreduced-arrival.rho` | Beat 3's guard over Contract C **un-reduced** — refused |
| `desk-accepts-nothing.rho` | the same three; a predicate none satisfies keeps nothing |
| `RUN-SHEET.md` | this page |
| `rholang-runtime/tests/assay_desk_demo.rs` | the CI gate that drives every command above |

## Related

* `demos/flt-foreign-exchange/` — the FLT feature's first demo: typed `${x}` holes destructuring a
  foreign term across a COMM (`foreign-exchange.rho`), and a bare term driven to normal form
  (`k-combinator.rho`).
* `demos/rholang-settlement/` — `where` guards over ground data in the REPL, and the account of
  defect D1 and its repair (`repl/tests/settlement_demo.rs`).
