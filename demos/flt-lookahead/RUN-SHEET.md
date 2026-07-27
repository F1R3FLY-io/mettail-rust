# The Computed Desk — filtering over values the machine computed

A live demonstration of RhoCalc's **`[*]` lookahead**: a send suffixed with `[*]` is not a send
at all but an **exploration**, and the values that arrive on its channel are the terminal terms
of every execution path the Rholang machine enumerated. A program can then filter over them with
an ordinary Foreign Language Term receive pattern — the same syntax it uses for values someone
sent it.

The demo exists to remove one specific illusion. `demos/flt-lambda-lab/04-desk.rho` and
`demos/flt-church-desk/desk-keeps-five.rho` both filter Church numerals, and every numeral in
them is a **constant a human transcribed**. They demonstrate that the pattern matcher works.
They demonstrate nothing about the machine's ability to compute the thing being matched. This
page's program contains no transcribed answer.

> Status: **VALIDATED end to end, 2026-07-26** — every command on this page was run and the
> transcript below is the observed one.
> The script is a CI gate: `rholang-runtime/tests/lookahead_demo.rs` drives the built `rhocalc`
> binary with this exact command line and asserts the observable, and the mechanism itself is
> gated by `rholang-runtime/tests/x7_lookahead_end_to_end.rs`.

---

## The claim, in one sentence

> Two λ-terms are β-reduced to normal form by the Rholang machine — inside a **speculative
> tuplespace**, one enumerated communication at a time — and the results are delivered onto an
> ordinary channel where an ordinary Rholang receive pattern filters them, in the **same
> reduction round**.

## What `[*]` means

```text
    x!(P)[*]    explore EVERY execution path of P; deliver each path's terminal term to x
    x!(P)[n]    explore at most n communications along every path; publish a resumable handle
                for every branch the bound cut short
```

`[n]` is the FIPS's bounded bracket and has **three** outcomes, not two — quiescent, truncated,
aborted — because *"this branch died"* and *"I stopped early, here is where to resume"* are
different facts and a consumer has to be able to tell them apart.

## The program

`demos/flt-lookahead/01-computed-desk.rho`, with the comment header elided:

```
@"results"!(lambda`((lam m. lam n. lam f. lam x. ((m, f), ((n, f), x)), lam f. lam x. (f, (f, x))), lam f. lam x. (f, (f, (f, x))))`)[*] |
@"results"!(lambda`((lam m. lam n. lam f. (m, (n, f)), lam f. lam x. (f, (f, x))), lam f. lam x. (f, (f, (f, x))))`)[*] |

for(@lambda`lam f. lam x. ${body}` <- @"results") {
  @"OUT"!(lambda`${body}`)
}
```

The two subjects are `plus 2 3` and `mult 2 3` in pure untyped λ-calculus — no numbers, no
arithmetic, only functions:

```math
\mathrm{plus} \equiv \lambda m.\lambda n.\lambda f.\lambda x.\; m\,f\,(n\,f\,x)
\qquad
\mathrm{mult} \equiv \lambda m.\lambda n.\lambda f.\; m\,(n\,f)
```
```math
\mathbf{2} \equiv \lambda f.\lambda x.\; f\,(f\,x)
\qquad
\mathbf{3} \equiv \lambda f.\lambda x.\; f\,(f\,(f\,x))
\qquad
\mathrm{plus}\;\mathbf{2}\;\mathbf{3} \;\twoheadrightarrow_\beta\; \mathbf{5}
\qquad
\mathrm{mult}\;\mathbf{2}\;\mathbf{3} \;\twoheadrightarrow_\beta\; \mathbf{6}
```

## The shape

```text
   @"results"!( ⟦plus 2 3⟧ )[*]                @"results"!( ⟦mult 2 3⟧ )[*]
              │                                            │
              │  lowers to  @"^spec-all"!( ⟦P⟧ , @"results" )  — a REQUEST, never a send of P
              ▼                                            ▼
   ╭───────────────────────── the request server ──────────────────────────╮
   │  an INSTALLED system process on ^spec-all (persistent: n requests,    │
   │  one continuation).  For each request:                                │
   │                                                                       │
   │    fund a fresh speculative sandbox from THIS deploy's phlogiston      │
   │    inject   ⟨the λ guest's installed Rho-net program⟩ | seed(⟦P⟧)      │
   │    enumerate E(S) breadth-first, firing one communication per step     │
   │    until every branch reaches quiescence                              │
   │    charge the host one token per committed COMM                        │
   ╰───────────────────────────────┬───────────────────────────────────────╯
                                   │
        ┌──────────────────────────┼───────────────────┬─────────────────────┐
        ▼                          ▼                   ▼                     ▼
   @"results"                ^spec-success        ^spec-delivery        ^spec-failure
   the BARE terminal         [trace, term]        [success,             [trace,
   term — one datum          per branch            truncated,            [code, message]]
   per success branch                              failure]              per dead branch
        │
        ▼
   for(@lambda`lam f. lam x. ${body}` <- @"results") { … }
   an ORDINARY FLT receive — it does not know a speculation produced its datum
```

Publishing the **bare** term on `@"results"` (rather than a `[trace, term]` pair) is what makes
that last line work verbatim. The provenance is on the companion channels for a program that
wants it, so nothing is lost and no consumer is forced to destructure a pair to read an answer.

## Running it

```
cargo build -p rholang-runtime --features rhocalc-runtime,lambda-runtime,calculator-runtime --bin rhocalc
RUST_MIN_STACK=8388608 target/debug/rhocalc demos/flt-lookahead/01-computed-desk.rho
```

Observed:

```
rhocalc — RhoCalc (Rholang 1.4) interpreter
source: demos/flt-lookahead/01-computed-desk.rho
comments: 47 retained on the COMMENTS channel
mode: process → running to rest on the f1r3node reducer (observing @"OUT")
  @"OUT" observations (1):
    [0] ⟦(1 (1 (1 (1 (1 0)))))⟧
  lookahead: 2 request(s) served · ^spec-success: 2 · ^spec-failure: 0 · ^spec-truncated: 0
```

`⟦(1 (1 (1 (1 (1 0)))))⟧` is the **body** of the Church numeral 5 — five applications of the
de-Bruijn-indexed `f` to `x`, which is what the receive republished after binding `${body}` out
of `lam f. lam x. ${body}`. The other computed numeral, 6, is still resting on `@"results"`:
one `for` consumes one datum, exactly as it would for two ordinary sends.

## What the audience should ask, and the answer

| question | answer |
|---|---|
| *"Is 5 in the source?"* | No. Search the file: it contains `plus`, `mult`, `two` and `three` spelled out as λ-terms and no numeral. |
| *"Could it be reporting its input back?"* | No, and it is structurally prevented. `x!(P)[*]` emits **one** send — the request — and never a send of `P` on `x` (`x5_lookahead_lowering.rs::a_lookahead_does_not_also_send_the_subject_on_the_channel`). The only data that ever rest on `@"results"` are terms the engine computed. |
| *"What if the engine were missing?"* | The request would **rest** on `^spec-all` and the interpreter would fail with `lookahead request(s) rested unserved`. It cannot silently publish nothing, and it cannot silently degrade to a single-path answer (`x5_lookahead_lowering.rs::an_unserved_lookahead_request_rests_and_is_reported`). |
| *"Is this just running the term once?"* | No. The branch's published trace is **403 steps** long for `plus 2 3` — 403 individually enumerated communications, each one chosen from `E(S)` by the search rather than by the scheduler (`x7_lookahead_end_to_end.rs::both_delivery_forms_are_published`). |
| *"Does it enumerate, or does it just follow one path?"* | It enumerates. Over `c!(1) \| c!(2) \| for(@x <- c){OUT!(x)}` — a genuine tuplespace conflict — the same engine returns **two** leaves, delivering `Int(1)` on one and `Int(2)` on the other (`s2_speculative_branching.rs`). λ returns one because λ is confluent. |
| *"What about a term with no normal form?"* | It says so. Ω under `[*]` reaches quiescence having computed nothing, and the branch is published as a trace-keyed **failure** naming the guest's own `^drive-fuel` channel — never as an empty answer (`x7_lookahead_end_to_end.rs::omega_reports_the_guest_evaluator_giving_up`). |
| *"Who pays for the exploration?"* | This deploy. The sandbox is funded from the host's remaining phlogiston and the host is charged one token per committed communication, so a runaway exploration exhausts the deploy and is rejected like any other over-budget program. There is no separate speculation budget and no new consensus parameter. |

## The failure modes it is arranged around

Two of them are worth stating out loud, because both would produce a demo that looked correct.

**1. The confluence trap.** λ-calculus is confluent, so *"drive the term once to quiescence and
wrap the answer"* returns the **right answer for every λ term**. It would pass every
λ-flavoured test anyone would think to write. It is nevertheless not `[*]`, because it never
enumerates the path set, and it silently returns one answer for a guest that has several. The
lowering is asserted **not** to emit the single-path `^drive` seed
(`x5_lookahead_lowering.rs::lookahead_does_not_lower_onto_the_single_path_drive`).

**2. The inert-subject trap.** A reflected foreign term is data: an `EList` of tags, containing
no send and no receive. Exploring one *without its guest's installed program* finds exactly one
leaf — the subject, unreduced — and publishing that leaf would put the program's own input on
the reply channel where it is indistinguishable from a normal form. The server therefore reads
the guest's fingerprint off the subject's own head tag and **refuses**, loudly, on `^spec-err`
if no evaluator is registered for it
(`x7_lookahead_end_to_end.rs::an_unregistered_guest_is_refused_loudly`).

## Where the parts live

| part | file |
|---|---|
| the surface and its lowering | `rholang-runtime/src/rhocalc_ast.rs` (the `PLookahead*` arms) |
| the wire — reserved channels, request seeds, the unserved-request readback | `rholang-runtime/src/lookahead.rs` |
| the branching search | `rholang-runtime/src/speculation/search.rs` |
| result assembly (reification, the three FIPS collections) | `rholang-runtime/src/speculation/delivery.rs` |
| the engine's request/response façade | `rholang-runtime/src/speculation/service.rs` |
| **the request server** — the two system processes | `rholang-runtime/src/speculation/server.rs` |
| the interpreter's installation of it | `rholang-runtime/src/bin/rhocalc.rs` (`lookahead_engine`) |
