# The Guarded Settlement Desk — RhoCalc `where` guards dispatching on F1r3node RSpace

A live REPL demonstration of semantic predicates (`where` clauses) in RhoCalc and of RhoCalc
applications dispatching via the rho-native integration onto F1r3node's RSpace. Stock RhoCalc —
no custom language definition. Every `exec` runs on a fresh in-memory Rho machine; the `step`
trace observes the production tuplespace one committed COMM at a time, so a recording and a live
run match on trace content. Every beat below reproduced identically over five consecutive runs
(2026-07-25) — with one exception, Beat 3's third command, which is nondeterministic for the
reason recorded there.

> Status: **VALIDATED end to end, 2026-07-25** — every command below was run by hand and every
> output on this page is the observed one, pinned. The whole script is now a CI gate:
> `repl/tests/settlement_demo.rs` drives the built `repl` binary with these exact command
> lines and asserts each beat's observable, plus a runtime-level readback for the "…and it is
> still on the book" half that the REPL's single-channel `OUT` view cannot show. A command
> line added or respelled here without matching coverage there fails the build
> (`every_run_sheet_command_line_is_driven_by_this_test`). Guard-spelling fallbacks are inline
> per beat and are **not** needed today — the shipped `<=` and infix-`*` spellings parse.
>
> ⚠ One beat is affected by a live defect: **Beat 3's third command is nondeterministic**
> (defect D1, detailed in that beat). Read it before presenting.

Launch (the repl package takes a startup language):

```
$ target/release/repl rhocalc
```

CI drives this same script through `env!("CARGO_BIN_EXE_repl")`, so the presenter's binary and
the gated one are built from one source. A `cargo build -p repl --bin repl` (debug) behaves
identically — only slower.

Load the desk bindings (or paste the two definitions from `settlement.env` manually):

```
RhoCalc> load-env demos/rhocalc-settlement/settlement.env
```

---

## Beat 0 — Orientation (30 s)

```
RhoCalc> info
```

Expected — the RUNTIME section names the language's INSTALLED runtime capabilities:

```
RUNTIME
  RhoMachine (default)
```

(This line prints capabilities, not the wrapper's internal staging: the two-stage
Dovetail+Rholang wrapper advertises exactly one backend, the machine, and selects it by
default. The Dovetail stage is visible only where it is still reached — cameo B.)

> "The rho calculus here is just another MeTTaIL language definition — and since the flip, its
> production semantics run on F1r3node's Rho machine."

## Beat 1 — Even arithmetic is machine work (1 min)

```
RhoCalc> exec 2u32 + 3u32
```

Expected: `OUT: [5] (1 value(s))`.

```
RhoCalc> exec 1 + 2
```

Expected: `OUT: [3] (1 value(s))` — and the *carrier* is the point. A numeral's carrier is a
function of the numeral (divergence I, `12704fc1`, 2026-07-25): a bare `1` is f1r3node's `GInt`,
exactly as `normalize_ground` says, and only the `n`-suffixed spelling `1n` is a `GBigInt`. Show
that too if the audience asks for arbitrary precision:

```
RhoCalc> exec 1n + 2n
```

Expected: `OUT: [BigInt(0x03)] (1 value(s))` — the raw big-int bytes resting on the tuplespace.

> Historical note: this beat read `OUT: [BigInt(0x03)]` for the bare `1 + 2` until divergence I
> re-baselined the wire carrier. No persisted RSpace state exists on this branch (the demo
> builds an in-memory runtime per invocation), so the re-baseline is invisible to everything
> except this line.

**Proves**: the host computes nothing (the A-S4 lowering purity result); the value is produced by
the machine's metered `EPlus` and read back off RSpace (the `@("OUT")!(v)` wrap).

> "One plus two never runs on my laptop's CPU path — it lowers to the machine's metered
> expression algebra, and what you see is literally the value resting on the tuplespace. Spell
> the numeral `1n` and you see its raw big-int bytes instead: the spelling picks the carrier."

## Beat 2 — Hello COMM, test-pinned (1 min)

```
RhoCalc> exec { for(x <- @("c")){*(x)} | @("c")!(@("OUT")!("p")) }
```

Expected: `OUT: ["p"] (1 value(s))` — the byte-exact subject of the committed zero-D-stage test
(`repl/tests/zero_dstage_exec.rs::admitted_rhocalc_exec_builds_no_dovetail_report` — Dovetail
counter delta 0, backend RhoMachine).

**Proves**: a rho-calculus COMM written in RhoCalc executes as a machine COMM with zero Dovetail
work.

> "This is the meta moment: the language models the rho calculus, and its communication rule is
> dispatched by an actual rho machine — a `for` and a send become a Receive and a Send on
> RSpace."

## Beat 3 — The desk: a guarded limit order (3 min — THE CORE)

```
RhoCalc> exec { desk | @("offer")!(42u32) }
```

Expected: `OUT: [42] (1 value(s))`.
(The shipped `<=` spelling parses — verified 2026-07-25, `the_shipped_guard_spellings_parse_and_lower`
— even though `<=` is *also* the persistent-bind arrow of `for(x <= chan)`. Should that
ambiguity ever resolve the other way, the fallback is `where px < 46u32`; the machine path is
ELte/ELt either way.)

```
RhoCalc> exec { desk | @("offer")!(55u32) }
```

Expected: `OUT: [] (0 value(s))` — the veto is VISIBLE as an empty observation channel.

```
RhoCalc> exec { desk | @("offer")!(55u32) | @("offer")!(42u32) }
```

Expected — ⚠ **read the defect note below before presenting**: `OUT: [42] (1 value(s))` is the
CORRECT answer (the 55 offer is never consumed; it stays on the book), but today this command
returns `OUT: [] (0 value(s))` a substantial fraction of the time: **12 × `[42]` and 8 × `[]`
over 20 consecutive runs** (measured 2026-07-25).

> ### ⚠ Defect D1 — a guard rejection does not backtrack to the next resting datum
>
> **What the semantics require.** A guarded receive is enabled by *any* resting datum that
> matches the pattern **and** satisfies the guard. With the 42 on the book the COMM is enabled,
> so resting is not quiescence — it is a stuck state the rho calculus does not admit. The
> expectation above is the specification; the implementation is incomplete.
>
> **Where it breaks.** The guard is not part of candidate SELECTION, only of candidate
> APPROVAL, and rejection retries the wrong axis:
>
> | site (`f1r3node-rust-mettail`) | what it does |
> |---|---|
> | `rspace++/src/rspace/space_matcher.rs` · `find_matching_data_candidate` | returns the FIRST datum matching **spatially**; the `where` guard is not consulted here |
> | `rspace++/src/rspace/space_matcher.rs` · `extract_first_match` | evaluates the guard via `Match::check_commit`; on rejection `continue`s to the next waiting **continuation** — never to the next **datum** |
> | `rspace++/src/rspace/rspace.rs` · `consume` | one `extract_data_candidates` pick, one `check_commit`; on `false` the continuation is installed and the data are left untouched |
>
> Because the pattern `@px` matches either offer, the outcome is decided entirely by WHICH
> datum the single pick returns — and that is not stable: pinning the arrival order does not
> pin it either. A program that produces the 42, then the 55, then installs the receive — so
> both offers are resting and no later produce can re-trigger the rendezvous — still rested 6
> times and settled 2 times over 8 consecutive runs. The stuck state is therefore FINAL, not
> merely early: the store is read at quiescence, with an enabled COMM left unfired.
>
> **Pinned, not narrated.** `repl/tests/settlement_demo.rs` ::
> `guard_rejection_does_not_backtrack_to_the_next_resting_datum` runs that fixed program 24
> times and requires BOTH outcomes to occur — the stuck one (the defect is real) and the
> settling one (the rendezvous really is enabled, so the stuck runs are stuck rather than
> impossible). It also fails on any THIRD outcome, which is what pins the part that never
> varies: no run consumes the 55, and no run fabricates a value. The test is written to FAIL
> once the matcher is repaired, so this beat gets revisited with it.
>
> **Presenting.** Either skip this command, or run it and say the true thing: the veto is
> absolute (the 55 is never consumed, in any run — `beat_3_two_offers_never_consume_the_inadmissible_one`),
> and the *other* offer's rendezvous is currently at the mercy of a matcher that stops at its
> first rejected candidate.

**Proves**: the `where` clause rides as `Receive.condition`; the machine matcher's
`check_commit` evaluates it purely — COMM-free — and a failed guard leaves the consume
uncommitted and the datum resting. Fail-closed veto, zero partial effects. (What it does *not*
yet prove is liveness for a second, admissible datum on the same channel — defect D1.)

## Beat 3b — The guard the machine never sees (1.5 min, optional)

Every guard so far is *payload-dependent*: it mentions `px`, so it cannot be decided until the
offer arrives. Ask what happens when a guard mentions nothing at all.

```
RhoCalc> exec { for(@px <- @("offer") where false implies false){@("OUT")!(px)} | @("offer")!(42u32) }
```

Expected: `OUT: [42] (1 value(s))` — `F ⇒ F` is vacuously true, so the receive commits.

The interesting part is not the answer, it is the **artifact**. `false implies false` mentions no
variable, so the compiler runs the machine's *own* guard evaluator on it at lowering time, gets
`true`, and records that by **not emitting `Receive.condition` at all**. The `where` clause is
simply absent from the compiled program: the matcher's

```rust
let Some(guard) = k.guard.as_ref() else { return true; };
```

short-circuit then answers `true` with no work, on every node, on play and on replay alike.

Contrast the mirror case:

```
RhoCalc> exec { for(@px <- @("offer") where true implies false){@("OUT")!(px)} | @("offer")!(42u32) }
```

Expected: `OUT: [] (0 value(s))` — and the guard is **still in the artifact, verbatim**. A guard
that is statically FALSE is only *reported* (`W1 GuardStaticallyFalse`, at DEBUG on
`mettail.lowering.guard`); it is never removed. A `for` that can never fire is not dead code — it
is a resting, observable continuation, present in the normal form, in the state hash, and in
storage. Removing it would change what a validator sees.

**Proves**: compile-time guard discharge (S-D0) is *one-sided* and *observationally inert*.
Only a provably-`true` binder-closed guard is elided, and eliding it is sound because an omitted
guard and a `true` guard drive `check_commit` to the identical verdict — mechanized as
`GuardDischargeSoundness.v`'s `discharge_preserves_the_fired_set`.

> "The compiler is allowed to answer a question the runtime was going to ask, but only when it
> can use the runtime's own evaluator to answer it, and only when the answer is yes. A 'no' it
> merely tells you about — because a receive that never fires is still part of the state."

> "The guard is not an if-statement in the body — the body never starts. The veto happens inside
> the machine's matcher, before the COMM commits, and the rejected offer is still on the book."

(The stronger reading — "…still on the book *for anyone else*" — is the liveness half, and that
is exactly what defect D1 currently withholds: another taker's rendezvous can be blocked by the
rejected datum rather than merely coexisting with it. Say the resting half, which is proven, and
leave the liveness half for when D1 is repaired.)

## Beat 4 — Atomic cross-channel settlement (2 min)

```
RhoCalc> exec { settle | @("bid")!(42u32) | @("ask")!(10u32) }
```

Expected: `OUT: [420] (1 value(s))` — both legs consumed atomically; the product computed by the
machine's `EMult`.
(The shipped infix `*` parses inside the guard — verified 2026-07-25 — even though `*` is also
the drop prefix. Fallback if that ambiguity ever resolves the other way: the budget guard
`where px + qty < 60u32`; guard-internal `+` and `*` are equally supported.)

```
RhoCalc> exec { settle | @("bid")!(60u32) | @("ask")!(10u32) }
```

Expected: `OUT: [] (0 value(s))` — 600 > 500: BOTH the bid and the ask remain resting. The REPL
shows only `OUT`, so the "both legs remain" half is asserted where it is observable — reading
`OUT`, `bid` and `ask` off the SAME quiescent store
(`beat_4_an_over_budget_trade_leaves_both_legs_resting`): `bid ↦ [60]`, `ask ↦ [10]`, `OUT ↦ []`.

**Proves**: multi-channel join + cross-bind guard evaluated once over the combined bindings —
all-or-nothing settlement.

> "Two channels, one atomic rendezvous. The guard sees both legs at once; if the trade violates
> the budget, neither leg is consumed. That is transactional matching as a language primitive."

## Beat 5 — SafeArith as a veto: division by zero cannot settle (1.5 min)

```
RhoCalc> exec { for(@q <- @("qty") where 100u32 / q >= 1u32){@("OUT")!(q)} | @("qty")!(0u32) }
```

Expected: `OUT: [] (0 value(s))` — no crash, no wrap: `DivisionByZero` inside the pure guard
evaluator is a guard-fail. The `0` is still on `@"qty"` afterwards
(`beat_5_the_undividable_datum_is_left_resting`): a failed partial operation vetoes the COMM
without disturbing the store.

```
RhoCalc> exec { for(@q <- @("qty") where 100u32 / q >= 1u32){@("OUT")!(q)} | @("qty")!(4u32) }
```

Expected: `OUT: [4] (1 value(s))`.

**Proves**: partial arithmetic inside a semantic predicate fails closed — the same discipline as
Calculator's SafeArith gate, enforced natively by the machine's matcher.

> "An unsafe computation in a guard doesn't throw — it simply makes the rewrite impossible.
> Fail-closed is the default physics, not an error handler."

## Beat 6 — Make the dispatch visible: the live COMM trace (2.5 min)

```
RhoCalc> step { desk | @("offer")!(42u32) }
```

Expected — exactly two steps, the committed COMM and the output it enables:

```
Computed:
  - backend: RhoMachine
  - artifact: RhoNormalizedAst
  - 2 reduction step(s) on the Rho machine

Reduction trace (step 0):
[Rho COMM] COMM[consume] "offer" ⇐  { 42 } ▸ cont "OUT"!(x-1)

  Use apply 0 to advance to the next reduction (1 remaining).
```

Then `apply 0` advances to the second and last step, and quiescence:

```
Applied graph edge → output
  [Rho output] OUT observes 42
```

(`x-1` in the continuation is the de Bruijn rendering of the bound `px`. A second `apply 0`
reports `next reduction 0 not found` — there is no third step; the trace is complete.)

```
RhoCalc> step { desk | @("offer")!(55u32) }
```

Expected — ZERO committed COMMs. With nothing to trace, the router falls back to the Layer-1
Dovetail graph, which has no rewrite from this term:

```
Computed:
  - backend: Dovetail
  - artifact: DovetailRunReport
  …
  - 0 rewrite edge(s)

  No rewrites from this term (already a normal form).
```

The veto is provably COMM-free: a live tracer recording every committed COMM on real RSpace saw
none — the transcript contains no `[Rho COMM]` node at all.

**Proves**: the Layer-2 stepper wraps the real f1r3node RSpace (one committed COMM per step,
deterministic seed); guard evaluation emitted no COMM.

> "This trace isn't a simulation — it's an observer bolted onto the production tuplespace,
> releasing one committed COMM per keypress. And when the guard vetoes, the recorder is empty:
> the predicate ran without a single COMM."

## Beat 7 — The universal mandate, fail-closed (1 min)

```
RhoCalc> exec [1, 2].length()
```

Expected — a typed error naming the construct, verbatim:

```
Error: RhoMachine backend for language RhoCalc could not build an AST invocation from the
checked Dovetail report: RhoCalc term could not be lowered to the Rho machine (A-S4
fail-closed lowering; no host fold-normalization fallback): UnsupportedProc("l.length() list
method")
```

(One line on the terminal; wrapped here. It is printed on stderr, so a piped recording shows it
interleaved with the trailing `Running RhoMachine backend...` from stdout — harmless.)

> "No silent host fallback exists anymore. Either it runs on the machine, or you get a typed
> refusal naming the construct."

## Optional cameo A — where `step` routes (1 min)

```
RhoCalc> lang lambda
Lambda> step --taus (lam x. x, lam a. lam b. a)
```

Expected — the **Layer-1 Dovetail rewrite graph**, not a τ trace:

```
Computed:
  - backend: Dovetail
  - artifact: DovetailRunReport
  …
  - 1 rewrite edge(s)

  Use apply 0 to apply a rewrite (1 available).
```

and `apply 0` performs the β step, printing `lam _ . lam _ . a`.

> ★ Corrected 2026-07-25. This cameo used to promise `[τ drive]`/`[τ subst]` nodes. It cannot
> deliver them, for two compounding reasons, and both are by design:
>
> 1. **`step` prefers Layer 1 whenever the term has a structural successor.** A β-redex has
>    one, so the router keeps the Dovetail rewrite graph and never reaches the Layer-2 live
>    COMM trace (`repl/src/repl.rs`, `exec_or_step_term`). Feed it a term with no Dovetail
>    successor (a normal form, or a genuine COMM) and Layer 2 does appear.
> 2. **τ classification covers only the in-Rho DRIVE families** — `^drive`, `^subst`,
>    `^drive-ac`, `^float` (`rholang-runtime/src/step.rs`, `TauChannelClassifier`). Today's
>    Layer-2 traces ride the report-carrying MATCH fallback, whose `sa:`/`loc:`/`cap:`/`col:`
>    channels are deliberately UNCLASSIFIED (the F5 pin), so they display as ordinary
>    `[Rho COMM]` nodes. `step --taus lam x. x` shows exactly that: real machinery COMMs on
>    `col:`/`cap:` channels, untagged.
>
> So the true statement — the reduction machinery *is* COMMs — is shown by stepping a Lambda
> normal form (`step --taus lam x. x`, whose trace is machinery COMMs on `col:`/`cap:`
> channels) rather than promised as a `[τ …]` label. The τ labels themselves are exercised by
> `rholang-runtime/src/step.rs`'s classifier tests, and the FLT demo's deferred Beat 4b is
> where a τ-labelled drive trace is planned to appear.

## Optional cameo B — the only non-machine site (1 min)

```
Lambda> lang calculator
Calculator> exec 5 / 0
```

Expected — `backend: Dovetail`, `artifact: DovetailRunReport`, and a result that names the
blocked predicate rather than a value:

```
Computed:
  - backend: Dovetail
  - artifact: DovetailRunReport
  - completeness: Complete
  …

Current Dovetail result:
DovetailRoots([Calculator::Int::DivInt, Calculator::Proc::ProcInt, …])
```

A semantic-predicate deferral lazily building the report: today's only non-Rho-machine runtime
site, the operational face of INV-14.

---

## Proof-points appendix (cite when asked "is that actually proven?")

| Demo claim | Mechanized backing |
|---|---|
| A failed guard commits nothing / fabricates nothing; a true guard commits | `GuardedCommSoundness.v`: `failed_guard_no_commit`, `missing_premise_no_commit`, `guarded_attempt_no_fabrication`, `true_guard_enabled_adds_output` |
| The machine COMM fires iff the guard is true; the complement cannot commit | `RhoGuardedCommSoundness.v`: `comm_fires_iff`, `comm_fires_implies_true_guard`, `rho_complement_no_commit`, `rho_guard_true_commits` |
| Semantic predicates emit no COMM (INV-14) | `WholeGsltInRhoOpCorrespondence.v`: `semantic_predicates_emit_no_comm`; doc 13 invariant table |
| The capstone operational correspondence (incl. iterated driving) | `WholeGsltInRhoOpCorrespondence.v`: `whole_gslt_in_rho_opcorrespondence`, `…_iterated` |
| Guard veto on the real runtime leaves data resting (single + join) | `rholang-runtime/tests/rho_guard_oracle.rs` (all four tests) |
| Admitted RhoCalc exec = zero Dovetail work; arithmetic on the machine | `repl/tests/zero_dstage_exec.rs`: `admitted_rhocalc_exec_builds_no_dovetail_report`, `a_s4_admitted_rhocalc_arithmetic_…` |
| No pre-computed values ride the injected call | `rholang-runtime/tests/rho_rhocalc_ast.rs` A-S4 tests + the byte-needle probe |
| Arithmetic is metered size-dependently | f1r3node `accounting/costs.rs` (bigint sum/mult/comparison costs) |
| Predicate deferral is the only non-machine runtime site | `zero_dstage_exec.rs`: the blocked-Calculator lazy-report test |
| Beat 3b's three claims (vacuous guard fires; its `where` is absent from the artifact; the refuted mirror keeps its guard and never fires) | `rholang-runtime/tests/guard_discharge_corpus.rs`: `the_run_sheets_beat_3b_is_exactly_what_the_compiler_does` |
| Every settlement guard is payload-dependent, so compile-time discharge leaves the demo byte-identical | `guard_discharge_corpus.rs`: `every_settlement_demo_guard_is_residual_so_the_demo_is_unchanged` |
| **Every beat on this page, as the audience sees it** | `repl/tests/settlement_demo.rs` — the built `repl` binary driven with these command lines |
| ⚠ Defect D1: a guard rejection does not backtrack to the next resting datum | `repl/tests/settlement_demo.rs`: `guard_rejection_does_not_backtrack_to_the_next_resting_datum` — 24 trials of one fixed program, requiring both the stuck and the settling outcome and rejecting any third |

## Prep status

- **P1 (this directory)**: DONE — `settlement.env` + this run sheet.
- **P2**: DONE — end-to-end RhoCalc-`where`-through-the-machine coverage now exists, in
  `repl/tests/settlement_demo.rs` rather than `rho_rhocalc_ast.rs`: single-bind pass/veto,
  cross-bind veto leaving BOTH legs, the `/0`-guard veto, and each one's resting-channel
  readback. Sibling suites cover the adjacent axes — `guard_discharge_corpus.rs` (the
  compile-time discharge differential, including Beat 3b verbatim) and `rho_implies_guard.rs`
  (the `implies` truth table on both evaluators).
- **P3**: DONE (2026-07-25) — the script was run verbatim; every `(to validate)` output above is
  replaced by the observed one; the shipped `<=` and infix-`*` guard spellings both parse; and
  piped stdin works (rustyline's non-tty path reads the script and suppresses the prompt, which
  is exactly what makes the CI gate possible). Two beats did not match and are corrected in
  place: Beat 1's bare-numeral carrier (divergence I) and cameo A's τ promise. One beat is
  defective: Beat 3's third command (defect D1).
- **P4 (open — NOT a prerequisite for presenting)**: defect D1. Repairing it means making the
  `where` guard part of candidate SELECTION rather than post-hoc approval — either by threading
  the guard into `find_matching_data_candidate` so a rejected datum is simply not a match, or by
  looping the guard check over remaining data before giving up. That is a change to
  `f1r3node-rust-mettail`'s RSpace, so it belongs to the f1r3node workstream, not to this demo.
- **Optional polish (not prerequisites)**: decimal rendering for BigInt observations
  (display-only); a consumed-cost readout in exec output (future work — metering runs, the REPL
  just doesn't print the number today; claim metering via the tests/source above).

## Logistics

12–15 min core + cameos. Every beat is a fresh one-liner — skippable without state damage. If
the build is unavailable, Beat 2's exact term and the guard-oracle outputs can be narrated from
the committed tests, and the Dovetail-only build's typed fail-closed error is itself
demonstrable.

Recording: piped stdin works — `printf '…\n…\n' | target/release/repl rhocalc` replays the whole
script non-interactively (rustyline detects the non-tty and reads lines directly), which is how
the CI gate drives it. For a recording that shows the typing, drive a tmux pane
(`tmux send-keys`) captured with `asciinema rec` (plus `script` as backup). Either way the
recording matches the gate, because the gate runs these exact lines.
