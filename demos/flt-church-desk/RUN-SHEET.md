# The Church Desk — a foreign language computed, filtered, and taken apart by the Rholang machine

A live demonstration of RhoCalc's **Foreign Language Term** (FLT) integration on F1r3node's Rho
machine. Two guest grammars are embedded in RhoCalc source. Their terms are **evaluated by the
Rholang machine itself**, not by a host interpreter; a **`where` clause selects** among the
results, leaving the rest resting on the channel; and a receive pattern whose hole sits **inside
the foreign term** takes one apart, binding a foreign sub-term out into Rholang.

Everything below is stock RhoCalc plus two bundled guests. There is no Rust harness in the demo
path: the presenter runs one interpreter binary on six committed `.rho` files.

> Status: **VALIDATED end to end, 2026-07-26** — every command on this page was run and every
> output below is the observed one. Each of the six files produced byte-identical output on three
> consecutive runs of a freshly built binary.
> The whole script is a CI gate: `rholang-runtime/tests/church_desk_demo.rs` drives the built
> `rhocalc` binary with these exact command lines and asserts each beat's observable, plus a
> runtime-level readback for the "…and the refused terms are still on the channel" half that the
> interpreter's single-channel `@"OUT"` view cannot show. A command line added or respelled here
> without matching coverage there fails the build
> (`every_run_sheet_command_line_is_driven_by_this_test`), and every transcript printed below is
> compared against a live run (`every_transcript_in_the_run_sheet_is_the_observed_output`).

---

## The claim, in one sentence

> A foreign language is embedded in Rholang; its terms are computed to a normal form by the
> Rholang machine, one committed COMM at a time; the results are filtered by a predicate the
> substrate decides; and a Rholang receive pattern reaches **inside** a foreign term to bind a
> sub-term of it out into Rholang.

## An opener is the grammar's own name

There is no nickname to memorize. An FLT opener is the **lower-cased name of the guest grammar**,
and the interpreter derives it from the language itself rather than from a hand-typed literal
(`derived_opener`, `rholang-runtime/src/bin/rhocalc.rs`):

| grammar | opener | what a bare term of it does |
|---|---|---|
| `CalculatorLanguage` | `` calculator`…` `` | evaluates to a **value** through the E3 fold dataflow — one installed Rholang contract per operator node |
| `LambdaLanguage` | `` lambda`…` `` | reduces to its **normal form** through the in-Rho quiescence driver — every `$\beta$` step a committed COMM |

## The shape

```
   ╭─────────────── written in the GUEST's own syntax ───────────────╮
   │                                                                 │
   │   calculator`2 + 3 * 4`           lambda`((mult, (plus …)) …)`  │
   │        Beat 0                            Beat 1                 │
   ╰────────────────┬──────────────────────────┬─────────────────────╯
                    │                          │
        E3 FOLD DATAFLOW                ^drive QUIESCENCE
   one Rholang contract per        β-reduction to a normal form,
     operator node, wired           fuel-bounded, with a ^fired
   through intermediate channels    ledger of every firing
                    │                          │
                    ▼                          ▼
                   14                   Church numeral 12
                                       (21 in-Rho β firings)

                             ─── Beat 2 ───
                  Ω = (λx. x x)(λx. x x)  ⟶  ^drive-fuel
                  the machine says plainly what it could not finish

   ╭──────────────────── three λ-terms rest here ────────────────────╮
   │                          @"results"                             │
   ╰───────┬─────────────────────────────────────────┬───────────────╯
           │                                         │
    Beats 3 & 4 — the FILTER                Beat 5 — the EXTRACTION

  for( @lambda`${r}` <- @"results"      for( @lambda`lam f. lam x. ${body}`
       where lambda`${r}` == … )             <- @"results" )
           │                                         │
           ▼                                         ▼
      @"OUT" = the one accepted           @"OUT" = the BODY, a sub-term
      numeral; the refused ones           of the foreign term, with the
      still resting, untouched            binders stripped by the match;
                                          the shapes that do not fit rest
```

Three mechanisms, doing three different jobs:

| | what it is | what it does |
|---|---|---|
| `` @lambda`${r}` `` | a receive **pattern** carrying one WHOLE-TERM hole | matches any reflected guest term and binds it to `r`. The foreign result becomes a value the RhoCalc program holds. A `${x}` hole is a secure typed-AST hole; it never splices strings (No-Injection). |
| `` where lambda`${r}` == … `` | the **guard** | re-quotes the captured term and **decides** it against a reference term. The decision is made by the substrate, not by the pattern. |
| `` @lambda`lam f. lam x. ${body}` `` | a receive pattern carrying a **NESTED** hole | matches only terms of that **shape**, and binds a **sub-term** — reached from under two guest binders — out into Rholang as an ordinary name. This is pattern matching *into* a foreign language. |

---

## Setup (do this before the audience arrives)

```
$ cargo build -p rholang-runtime --bin rhocalc --features "rhocalc-runtime lambda-runtime calculator-runtime"
```

All three features are required by the `rhocalc` bin target: `rhocalc-runtime` pulls in the
generated RhoCalc language and its AST-first lowering; `lambda-runtime` and `calculator-runtime`
pull in the two production grammars the interpreter registers as guests. The build takes a couple
of minutes cold. Everything after this is instant.

CI drives the same binary through `env!("CARGO_BIN_EXE_rhocalc")`, so the presenter's binary and
the gated one are built from one source.

★ **No run line below needs a `RUST_MIN_STACK` prefix, and none carries one.** Every run line on
this page used to be prefixed `RUST_MIN_STACK=134217728`, because the λ-guest's reduction on terms
this size once recursed deeper than the default thread stack allowed. That is no longer true, and
the sheet no longer says it is: the gate now asserts the **absence** of the prefix
(`no_run_line_in_the_sheet_carries_a_stack_prefix`), measured against a live run of each beat.

Two reasons the change is worth a sentence rather than a silent deletion:

* A run sheet that tells a presenter to set a resource knob is teaching them that the knob is part
  of the program. It is not — it never was. It was a symptom of a traversal that consumed native
  stack in proportion to the size of the term it was walking, and the fix belonged in the
  traversal.
* The prefix was also **misleading about where the cost was**. `RUST_MIN_STACK` resizes *spawned*
  threads only; it cannot resize a main thread, whose size is fixed by `ulimit -s` before `main`
  is entered. So on any beat whose cost fell on the main thread — parsing and lowering both do —
  the prefix was inert, and a presenter who trusted it would have been debugging the wrong knob.

Run every command from the workspace root.

---

## Beat 0 — a foreign language, evaluated as real arithmetic by the machine (1 min)

Start here because it needs no explanation at all. The file is one line of the **Calculator**
grammar, embedded in a RhoCalc program.

```
$ target/debug/rhocalc demos/flt-church-desk/calculator.rho
```

```
rhocalc — RhoCalc (Rholang 1.4) interpreter
source: demos/flt-church-desk/calculator.rho
comments: 5 retained on the COMMENTS channel
mode: term → evaluating on the f1r3node reducer (guest `calculator`, E3 fold dataflow)
  value on @"OUT" (1):
    [0] 14
```

Say: **"That is not Rholang. It is the Calculator grammar, embedded verbatim, and the machine just
evaluated it."** Two things worth landing:

1. **`14`, not `20`.** Operator precedence came from the *guest's* grammar, not from a re-parse.
2. **Nothing was string-spliced.** The text between the back-ticks went to the Calculator's own
   reflector as a typed AST. That is the No-Injection guarantee, and it is why an FLT is safe in a
   way that string interpolation is not.

Each operator became one installed Rholang contract call, wired through intermediate channels in
post-order — the E3 **fold dataflow**. The arithmetic is machine work, not a host fold.

---

## Beat 1 — the λ-calculus has no numbers, so the machine computes with functions (4 min)

**Show the term as written.** This is the hook.

```
$ tail -1 demos/flt-church-desk/arithmetic.rho
```

```
lambda`((lam m. lam n. lam f. (m, (n, f)), ((lam m. lam n. lam f. lam x. ((m, f), ((n, f), x)), lam f. lam x. (f, x)), lam f. lam x. (f, (f, x)))), ((lam m. lam n. lam f. lam x. ((m, f), ((n, f), x)), lam f. lam x. (f, (f, x))), lam f. lam x. (f, (f, x))))`
```

That is `$\mathrm{mult}\;(\mathrm{plus}\;1\;2)\;(\mathrm{plus}\;2\;2)$` — in other words
`$3 \times 4$` — written in the untyped `$\lambda$`-calculus, where `(f, a)` is application. The
`$\lambda$`-calculus has no numbers, so a number is **encoded as a function**: the Church numeral
`$n$` is the function that applies its first argument `$n$` times.

```math
\overline{n} \;=\; \lambda f.\, \lambda x.\, \underbrace{f\,(f\,(\cdots (f}_{n \text{ times}}\;x)\cdots))
```

```math
\mathrm{plus} \;=\; \lambda m.\,\lambda n.\,\lambda f.\,\lambda x.\; m\,f\,(n\,f\,x)
\qquad\qquad
\mathrm{mult} \;=\; \lambda m.\,\lambda n.\,\lambda f.\; m\,(n\,f)
```

Addition and multiplication are not primitives here. They are **consequences of substitution**.

```
$ target/debug/rhocalc demos/flt-church-desk/arithmetic.rho
```

```
rhocalc — RhoCalc (Rholang 1.4) interpreter
source: demos/flt-church-desk/arithmetic.rho
comments: 11 retained on the COMMENTS channel
mode: term → reducing to normal form on the f1r3node reducer
  normal form on @"OUT" (1):
    [0] ⟦λ.λ.(1 (1 (1 (1 (1 (1 (1 (1 (1 (1 (1 (1 0))))))))))))⟧
        = Church numeral 12
  ^fired ledger: ["Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta", "Beta"]   (21 in-Rho rewrite firing(s))
  ^drive-err: 0 datum(a) · ^drive-fuel: 0 datum(a)   (both empty ⟹ terminated by quiescence)
```

Three things to point at, in order:

1. **`= Church numeral 12`.** `$3 \times 4 = 12$`, arrived at with no arithmetic operation anywhere
   in the system — only `$\beta$`-reduction. The interpreter *names* the shape it sees; it does not
   compute it. Count the `1`s in the normal form and there are twelve.
2. **★ `(21 in-Rho rewrite firing(s))` — this is the receipt.** Twenty-one `$\beta$` steps fired,
   each one a **committed communication on RSpace**. This line is the answer to "how do I know the
   Rholang machine did this, and not some host-side interpreter?": a host reduction would leave the
   ledger empty. Every entry is `"Beta"` — no other rewrite family contributed.
3. **`^drive-err: 0 · ^drive-fuel: 0`.** Both empty, so the reduction stopped because it reached a
   normal form — **quiescence** — and not because it ran out of budget. Which brings us to:

---

## Beat 2 — and when it cannot finish, it says so (2 min)

```
$ target/debug/rhocalc demos/flt-church-desk/divergence.rho
```

```
rhocalc — RhoCalc (Rholang 1.4) interpreter
source: demos/flt-church-desk/divergence.rho
comments: 7 retained on the COMMENTS channel
mode: term → reducing to normal form on the f1r3node reducer
error: the term did not reach a normal form — reduction fuel exhausted
  the term is non-terminating or exceeds the per-path reduction budget
  stuck redex(es): ⟦(λ.(0 0) λ.(0 0))⟧
```

`$\Omega = (\lambda x.\, x\,x)(\lambda x.\, x\,x)$` `$\beta$`-reduces to **itself**, forever. The
in-Rho driver is fuel-bounded, so it stops — and the important part is what it does then:

* it **names the redex** it could not finish, on the `^drive-fuel` channel;
* it publishes **no normal form at all**, rather than handing back a half-reduced term as if it
  were an answer;
* it exits `70`, distinct from a parse error (`65`) and from success (`0`).

Say: **"Run-to-completion that cannot complete reports. It does not hang, and it does not lie."**
This is the beat that makes Beat 1's `^drive-fuel: 0` mean something.

---

## Beat 3 — a `where` guard selects one result and leaves the rest resting (3 min)

Three Church numerals rest on one channel — 5, 6, and 0. A `where` clause picks one.

```
$ target/debug/rhocalc demos/flt-church-desk/desk-keeps-five.rho
```

```
rhocalc — RhoCalc (Rholang 1.4) interpreter
source: demos/flt-church-desk/desk-keeps-five.rho
comments: 6 retained on the COMMENTS channel
mode: process → running to rest on the f1r3node reducer (observing @"OUT")
  @"OUT" observations (1):
    [0] ⟦λ.λ.(1 (1 (1 (1 (1 0)))))⟧
        = Church numeral 5
```

The desk kept **Church 5**. The other two were **not consumed**: they are still on `@"results"`
when the program comes to rest. The interpreter's view is single-channel, so it cannot show you
that — the CI gate reads a second channel of the same quiescent store and asserts it
(`beat_3_the_desk_keeps_five_and_leaves_six_and_zero_resting`):

| | on `@"OUT"` | still resting on `@"results"` |
|---|---|---|
| `desk-keeps-five.rho` | Church 5 | Church 6, Church 0 |

---

## Beat 4 — one changed token, a different answer, the same resting set (2 min)

`desk-keeps-six.rho` is the previous file with **one token changed**, in the guard. Same three
terms, same channel, same receive pattern, same order in the file.

```
$ target/debug/rhocalc demos/flt-church-desk/desk-keeps-six.rho
```

```
rhocalc — RhoCalc (Rholang 1.4) interpreter
source: demos/flt-church-desk/desk-keeps-six.rho
comments: 9 retained on the COMMENTS channel
mode: process → running to rest on the f1r3node reducer (observing @"OUT")
  @"OUT" observations (1):
    [0] ⟦λ.λ.(1 (1 (1 (1 (1 (1 0))))))⟧
        = Church numeral 6
```

**Run them back to back.** Two things follow, and neither is arguable:

1. **The guard is genuinely DECIDED, not failing closed.** A guard the substrate could not decide
   would refuse everything, and this file would publish nothing. A *vacuous* guard would return the
   same datum in both files. Neither happened.
2. **Church 5 was resting on `@"results"` during this run all along**, and Church 6 was resting
   during the previous one. The desk **selects out of** the resting set; it does not consume it.

| | on `@"OUT"` | still resting on `@"results"` |
|---|---|---|
| `desk-keeps-six.rho` | Church 6 | Church 5, Church 0 |

The gate asserts that the two files differ in exactly one program line and that the line is the
`where` clause (`beats_3_and_4_differ_only_in_the_guard`), so the pair cannot quietly start
differing somewhere else and keep passing.

---

## Beat 5 — ★ the receive pattern reaches *inside* the foreign term (4 min)

This is the one to slow down for.

```
$ tail -7 demos/flt-church-desk/destructure.rho
```

```
@"results"!(lambda`lam f. lam x. (f, (f, (f, (f, (f, x)))))`) |
@"results"!(lambda`lam x. x`) |
@"results"!(lambda`(lam x. x, lam y. y)`) |

for(@lambda`lam f. lam x. ${body}` <- @"results") {
  @"OUT"!(body)
}
```

Look at the receive pattern. It is itself a foreign term — and its hole is **not** the whole term.
`${body}` sits **under two guest binders**, at depth 2. So the pattern says two things at once:
*match only λ-terms shaped* `$\lambda f.\,\lambda x.\,\_$`, *and bind whatever is in that
position*. Three terms are resting; only the first has the shape.

```
$ target/debug/rhocalc demos/flt-church-desk/destructure.rho
```

```
rhocalc — RhoCalc (Rholang 1.4) interpreter
source: demos/flt-church-desk/destructure.rho
comments: 12 retained on the COMMENTS channel
mode: process → running to rest on the f1r3node reducer (observing @"OUT")
  @"OUT" observations (1):
    [0] ⟦(1 (1 (1 (1 (1 0)))))⟧
```

What came out is the numeral's **body**, not the numeral: the two binders were stripped away by the
match, and the five applications that remain are the answer's shape. **The structural match is the
decode.** Read `(1 (1 (1 (1 (1 0)))))` as `$f\,(f\,(f\,(f\,(f\;x))))$` — five applications, so the
term was Church 5. The `1`s and `0` are de Bruijn indices: `1` is the outer binder `f`, `0` the
inner binder `x`.

And the two that do not fit were **refused, not consumed**:

| resting term | shape | outcome |
|---|---|---|
| `lam f. lam x. (f, (f, (f, (f, (f, x)))))` | two binders | **matched** — body bound out |
| `lam x. x` | one binder | refused, still on `@"results"` |
| `(lam x. x, lam y. y)` | an application, no binder at its head | refused, still on `@"results"` |

A structurally blind pattern would have consumed one of them; the gate asserts both are still
resting (`beat_5_the_shapes_that_do_not_fit_are_refused_and_rest`), and separately that the
published body is a **strict sub-term** of the numeral it came out of
(`beat_5_the_published_body_is_a_strict_sub_term_of_the_matched_numeral`).

Say: **"Rholang just pattern-matched into another language's syntax tree, at depth, and pulled a
piece of it out."**

---

## What each beat rules out

No single defect produces all six outcomes, which is why the demo is six files and not one:

| a defect that… | would be caught by |
|---|---|
| computed the arithmetic on the host | Beat 1's `^fired` ledger, which would be empty |
| let a term run forever, or quietly returned it half-reduced | Beat 2 |
| admitted everything (a vacuous guard) | Beats 3 & 4 returning the same datum |
| refused everything (a guard the substrate cannot decide) | Beats 3 & 4 both publishing nothing |
| consumed the candidates it refused | the resting-channel readback in Beats 3, 4 and 5 |
| matched the foreign term loosely, ignoring its shape | Beat 5, where two of three terms are refused |
| bound the whole term rather than the sub-term | Beat 5's strict-sub-term assertion |

## If something goes wrong live

| symptom | cause | fix |
|---|---|---|
| `has overflowed its stack` | a regression — no beat on this page should be able to produce this | do **not** paper over it with `RUST_MIN_STACK`; that knob does not reach a main thread at all. Report it: `rholang-runtime/tests/stack_depth_gate.rs` is the gate that is supposed to catch it |
| `unknown guest language ⌜…⌝` | an opener was mistyped | an opener is the lower-cased grammar name: `calculator`, `lambda` |
| a beat prints a different numeral | the binary is stale | rebuild with the setup line; the bin's required features changed on 2026-07-26 |

## Files

| file | beat | program lines |
|---|---|---|
| `calculator.rho` | 0 | 1 |
| `arithmetic.rho` | 1 | 1 |
| `divergence.rho` | 2 | 1 |
| `desk-keeps-five.rho` | 3 | 5 |
| `desk-keeps-six.rho` | 4 | 5 |
| `destructure.rho` | 5 | 6 |

The files are deliberately almost all program: the explanation lives on this page, because this
page is what the presenter reads and the files are what the audience sees on screen. The gate puts
a number on that (`the_demo_files_are_mostly_program_not_commentary`).
