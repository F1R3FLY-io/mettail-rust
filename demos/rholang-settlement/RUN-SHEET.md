# The Guarded Settlement Desk — Rholang `where` guards dispatching on F1r3node RSpace

A live REPL demonstration of semantic predicates (`where` clauses) in Rholang and of Rholang
applications dispatching via the rho-native integration onto F1r3node's RSpace. Stock Rholang —
no custom language definition. Every `exec` runs on a fresh in-memory Rho machine; the `step`
trace observes the production tuplespace one committed COMM at a time, so a recording and a live
run match on trace content. Every beat below reproduces identically over consecutive runs
(2026-07-25; Beat 3's third command re-validated 2026-07-26 — see its note).

> Status: **VALIDATED end to end, 2026-07-25** — every command below was run by hand and every
> output on this page is the observed one, pinned. The whole script is now a CI gate:
> `repl/tests/settlement_demo.rs` drives the built `repl` binary with these exact command
> lines and asserts each beat's observable, plus a runtime-level readback for the "…and it is
> still on the book" half that the REPL's single-channel `OUT` view cannot show. A command
> line added or respelled here without matching coverage there fails the build
> (`every_run_sheet_command_line_is_driven_by_this_test`). Guard-spelling fallbacks are inline
> per beat and are **not** needed today — the shipped `<=` and infix-`*` spellings parse.
>
> ★ **No live defects.** Beat 3's third command used to be nondeterministic (defect D1); the
> matcher was repaired on 2026-07-26 and the beat is deterministic. Every expected output on
> this page is now unqualified.
>
> ★ **RE-VALIDATED 2026-07-28 — and this page carries the only mixed-precedence arithmetic in
> `demos/`.** Twenty-one defects closed that day across two repositories, among them an
> operator-precedence overhaul (`3ff1c98b`…`ce887d0b`) that rewrote every bundled language's
> binding-power ladder: Rholang's eighteen operators went from eighteen levels to nine, matching
> `rholang-rs/rholang-tree-sitter/grammar.js` exactly. A census over every `.rho` file and every
> run sheet in `demos/` finds the only expressions that mix operators of *different* levels
> here — `px * qty <= 500u32` and `@("OUT")!(px * qty)` in `settlement.env`, `100u32 / q >= 1u32`
> in Beat 5, `false implies false` / `true implies false` in Beat 3b — so this is the page the
> overhaul could have moved. It did not: `*` and `/` still bind tighter than every comparison,
> and `implies` was not re-levelled at all. All 24 cells of `repl/tests/settlement_demo.rs` pass
> at `6eec833d`, including the four that drive exactly those expressions
> (`beat_1_arithmetic_is_computed_by_the_machine`,
> `beat_4_the_cross_channel_join_settles_or_refuses_atomically`,
> `beat_5_division_by_zero_inside_a_guard_is_a_veto_not_a_crash`,
> `beat_3b_the_vacuous_guard_commits_and_the_refuted_one_never_does`).

Launch (the repl package takes a startup language):

```
$ target/release/repl rholang
```

CI drives this same script through `env!("CARGO_BIN_EXE_repl")`, so the presenter's binary and
the gated one are built from one source. A `cargo build -p repl --bin repl` (debug) behaves
identically — only slower.

Load the desk bindings (or paste the two definitions from `settlement.env` manually):

```
Rholang> load-env demos/rholang-settlement/settlement.env
```

---

## Beat 0 — Orientation (30 s)

```
Rholang> info
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
Rholang> exec 2u32 + 3u32
```

Expected: `OUT: [5] (1 value(s))`.

```
Rholang> exec 1 + 2
```

Expected: `OUT: [3] (1 value(s))` — and the *carrier* is the point. A numeral's carrier is a
function of the numeral (divergence I, `12704fc1`, 2026-07-25): a bare `1` is f1r3node's `GInt`,
exactly as `normalize_ground` says, and only the `n`-suffixed spelling `1n` is a `GBigInt`. Show
that too if the audience asks for arbitrary precision:

```
Rholang> exec 1n + 2n
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
Rholang> exec { for(x <- @("c")){*(x)} | @("c")!(@("OUT")!("p")) }
```

Expected: `OUT: ["p"] (1 value(s))` — the byte-exact subject of the committed zero-D-stage test
(`repl/tests/zero_dstage_exec.rs::admitted_rholang_exec_builds_no_dovetail_report` — Dovetail
counter delta 0, backend RhoMachine).

**Proves**: a rho-calculus COMM written in Rholang executes as a machine COMM with zero Dovetail
work.

> "This is the meta moment: the language models the rho calculus, and its communication rule is
> dispatched by an actual rho machine — a `for` and a send become a Receive and a Send on
> RSpace."

## Beat 3 — The desk: a guarded limit order (3 min — THE CORE)

```
Rholang> exec { desk | @("offer")!(42u32) }
```

Expected: `OUT: [42] (1 value(s))`.
(The shipped `<=` spelling parses — verified 2026-07-25, `the_shipped_guard_spellings_parse_and_lower`
— even though `<=` is *also* the persistent-bind arrow of `for(x <= chan)`. Should that
ambiguity ever resolve the other way, the fallback is `where px < 46u32`; the machine path is
ELte/ELt either way.)

```
Rholang> exec { desk | @("offer")!(55u32) }
```

Expected: `OUT: [] (0 value(s))` — the veto is VISIBLE as an empty observation channel.

```
Rholang> exec { desk | @("offer")!(55u32) | @("offer")!(42u32) }
```

Expected: `OUT: [42] (1 value(s))` — the guard vetoes the 55, the matcher moves on to the next
resting datum, and the 42 settles. The 55 is never consumed; it stays on the book.

This is the beat that says the veto is a *selection* criterion and not merely an *approval*
stamp. A guarded receive is enabled by *any* resting datum that matches the pattern **and**
satisfies the guard, so with the 42 on the book the COMM is enabled — and an enabled COMM
fires. Resting here would not be quiescence, it would be a stuck state the rho calculus does
not admit.

> ### ★ How this beat became deterministic — defect D1, repaired 2026-07-26
>
> Until 2026-07-26 this command returned `OUT: [] (0 value(s))` a substantial fraction of the
> time — **12 × `[42]` and 8 × `[]` over 20 consecutive runs** (measured 2026-07-25). The
> guard was part of candidate APPROVAL but not of candidate SELECTION, so rejection retried
> the wrong axis: `space_matcher.rs::find_matching_data_candidate` returned the first datum
> matching **spatially**, `extract_first_match` then evaluated the guard via
> `Match::check_commit` and on rejection advanced to the next waiting **continuation** — never
> to the next **datum** — and `rspace.rs::locked_consume` had the same shape. Because `@px`
> matches either offer, the outcome was decided entirely by which datum the single pick
> returned, and that was not stable even with the arrival order pinned.
>
> **The repair** (`f1r3node-rust-mettail` `feature/mettail`, `6bc58743` + `5d37f67e`):
> `SpaceMatcher::extract_guarded_data_candidates` is one depth-first search over the
> candidate-selection tree with the guard evaluated at the leaf, returning the lexicographically
> least selection that satisfies both the spatial patterns and the guard. The selection *order*
> is unchanged; the *search* is completed. Every COMM-firing path uses it — play consume, play
> produce, replay consume, replay produce — and candidate order is hoisted into
> `rspace::candidate_order` so play and replay agree by construction. Selection is a pure
> function of tuplespace *content* and the continuation: store insertion order no longer leaks
> into the outcome, which is why this beat is now reproducible rather than merely likely.
>
> **Pinned, not narrated.** `repl/tests/settlement_demo.rs` ::
> `guard_rejection_backtracks_to_the_next_resting_datum` runs the equivalent fixed program 24
> times in *each* arrival order and requires the settling outcome every single time. It fails
> loudly on the old stuck outcome (D1 has returned) and on any third outcome — no run may
> consume the 55, and no run may fabricate a value.

**Proves**: the `where` clause rides as `Receive.condition`; the machine matcher's
`check_commit` evaluates it purely — COMM-free — a failed guard leaves that datum resting, and
the search moves on to the next candidate rather than abandoning the rendezvous. Fail-closed
veto, zero partial effects, and liveness for a second admissible datum on the same channel.

## Beat 3b — The guard the machine never sees (1.5 min, optional)

Every guard so far is *payload-dependent*: it mentions `px`, so it cannot be decided until the
offer arrives. Ask what happens when a guard mentions nothing at all.

```
Rholang> exec { for(@px <- @("offer") where false implies false){@("OUT")!(px)} | @("offer")!(42u32) }
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
Rholang> exec { for(@px <- @("offer") where true implies false){@("OUT")!(px)} | @("offer")!(42u32) }
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

(The stronger reading — "…still on the book *for anyone else*" — is the liveness half, and it
holds too, since defect D1 was repaired on 2026-07-26: a rejected datum coexists with the
rendezvous instead of blocking it, so another taker whose guard admits it still fires. Beat 3's
third command is exactly that claim in one line.)

## Beat 4 — Atomic cross-channel settlement (2 min)

```
Rholang> exec { settle | @("bid")!(42u32) | @("ask")!(10u32) }
```

Expected: `OUT: [420] (1 value(s))` — both legs consumed atomically; the product computed by the
machine's `EMult`.
(The shipped infix `*` parses inside the guard — verified 2026-07-25 — even though `*` is also
the drop prefix. Fallback if that ambiguity ever resolves the other way: the budget guard
`where px + qty < 60u32`; guard-internal `+` and `*` are equally supported.)

```
Rholang> exec { settle | @("bid")!(60u32) | @("ask")!(10u32) }
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
Rholang> exec { for(@q <- @("qty") where 100u32 / q >= 1u32){@("OUT")!(q)} | @("qty")!(0u32) }
```

Expected: `OUT: [] (0 value(s))` — no crash, no wrap: `DivisionByZero` inside the pure guard
evaluator is a guard-fail. The `0` is still on `@"qty"` afterwards
(`beat_5_the_undividable_datum_is_left_resting`): a failed partial operation vetoes the COMM
without disturbing the store.

```
Rholang> exec { for(@q <- @("qty") where 100u32 / q >= 1u32){@("OUT")!(q)} | @("qty")!(4u32) }
```

Expected: `OUT: [4] (1 value(s))`.

**Proves**: partial arithmetic inside a semantic predicate fails closed — the same discipline as
Calculator's SafeArith gate, enforced natively by the machine's matcher.

> "An unsafe computation in a guard doesn't throw — it simply makes the rewrite impossible.
> Fail-closed is the default physics, not an error handler."

## Beat 6 — Make the dispatch visible: the live COMM trace (2.5 min)

```
Rholang> step { desk | @("offer")!(42u32) }
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
Rholang> step { desk | @("offer")!(55u32) }
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
Rholang> exec {1 : 10}.values()
```

Expected — the reducer's typed error naming the method, verbatim:

```
Running RhoMachine backend... exit

Error: inj: ReduceError("Unimplemented method: values")
```

> **⚠ Changed 2026-07-26 (C1).** This beat used to run `exec [1, 2].length()`. That is no longer
> a refusal: **C1** routes the collection methods to the Rholang interpreter's own method table,
> so `[1, 2].length()` now answers `2` **on the reducer** — which is the mandate working, not
> failing. The beat needs an operation the machine genuinely cannot perform, and `.values()` is
> the nearest one: structural lowering emits `EMethod`, then `reduce.rs::method_table` rejects it
> because the table provides `keys` but not `values`. If you want to show BOTH halves, run
> `exec [1, 2].length()` first (it answers `OUT: [2]`) and then
> `exec {1 : 10}.values()` — the contrast is the point of the beat.

(One line on the terminal; wrapped here. It is printed on stderr, so a piped recording shows it
interleaved with the trailing `Running RhoMachine backend...` from stdout — harmless.)

> "No silent host fallback exists anymore. The machine either computes the method or returns its
> typed refusal naming it."

## Optional cameo A — where `step` routes (1 min)

```
Rholang> lang lambda
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
| Admitted Rholang exec = zero Dovetail work; arithmetic on the machine | `repl/tests/zero_dstage_exec.rs`: `admitted_rholang_exec_builds_no_dovetail_report`, `a_s4_admitted_rholang_arithmetic_…` |
| No pre-computed values ride the injected call | `rholang-runtime/tests/rho_rholang_ast.rs` A-S4 tests + the byte-needle probe |
| Arithmetic is metered size-dependently | f1r3node `accounting/costs.rs` (bigint sum/mult/comparison costs) |
| Predicate deferral is the only non-machine runtime site | `zero_dstage_exec.rs`: the blocked-Calculator lazy-report test |
| Beat 3b's three claims (vacuous guard fires; its `where` is absent from the artifact; the refuted mirror keeps its guard and never fires) | `rholang-runtime/tests/guard_discharge_corpus.rs`: `the_run_sheets_beat_3b_is_exactly_what_the_compiler_does` |
| Every settlement guard is payload-dependent, so compile-time discharge leaves the demo byte-identical | `guard_discharge_corpus.rs`: `every_settlement_demo_guard_is_residual_so_the_demo_is_unchanged` |
| **Every beat on this page, as the audience sees it** | `repl/tests/settlement_demo.rs` — the built `repl` binary driven with these command lines |
| A guard rejection backtracks to the next resting datum, so an enabled COMM is never stranded (defect D1, repaired 2026-07-26) | `repl/tests/settlement_demo.rs`: `guard_rejection_backtracks_to_the_next_resting_datum` — 24 trials of one fixed program in each arrival order, requiring the settling outcome every time and rejecting both the stuck outcome and any third. Matcher-level: f1r3node `rspace++/tests/guarded_matching_tests.rs` (15 tests); reducer-level: `rholang/…/reduce_spec.rs` (`6bc58743` + `5d37f67e`) |
| …and the search still fails CLOSED when the guard admits nothing: everything rests, nothing is fabricated | `repl/tests/settlement_demo.rs`: `a_guard_no_resting_datum_satisfies_exhausts_the_search_and_rests` — the negative control that also proves the row above is not vacuous |

## Prep status

- **P1 (this directory)**: DONE — `settlement.env` + this run sheet.
- **P2**: DONE — end-to-end Rholang-`where`-through-the-machine coverage now exists, in
  `repl/tests/settlement_demo.rs` rather than `rho_rholang_ast.rs`: single-bind pass/veto,
  cross-bind veto leaving BOTH legs, the `/0`-guard veto, and each one's resting-channel
  readback. Sibling suites cover the adjacent axes — `guard_discharge_corpus.rs` (the
  compile-time discharge differential, including Beat 3b verbatim) and `rho_implies_guard.rs`
  (the `implies` truth table on both evaluators).
- **P3**: DONE (2026-07-25) — the script was run verbatim; every `(to validate)` output above is
  replaced by the observed one; the shipped `<=` and infix-`*` guard spellings both parse; and
  piped stdin works (rustyline's non-tty path reads the script and suppresses the prompt, which
  is exactly what makes the CI gate possible). Two beats did not match and are corrected in
  place: Beat 1's bare-numeral carrier (divergence I) and cameo A's τ promise. One beat was
  defective — Beat 3's third command (defect D1) — and is now repaired; see P4.
- **P4**: DONE (2026-07-26) — defect D1 is repaired. The `where` guard is now part of candidate
  SELECTION rather than post-hoc approval: `SpaceMatcher::extract_guarded_data_candidates`
  searches the whole selection tree with the guard at the leaf and returns the lexicographically
  least admissible selection. Landed in `f1r3node-rust-mettail` `feature/mettail` (`6bc58743`
  fix, `5d37f67e` tests), as anticipated — it was a change to that repo's RSpace, not to this
  demo. Mettail-side follow-through: Beat 3's third command restored to its unqualified
  `OUT: [42] (1 value(s))`, and `repl/tests/settlement_demo.rs` tightened from a
  both-outcomes-must-occur witness to an every-trial-must-settle regression guard.
- **Optional polish (not prerequisites)**: decimal rendering for BigInt observations
  (display-only); a consumed-cost readout in exec output (future work — metering runs, the REPL
  just doesn't print the number today; claim metering via the tests/source above).

## Logistics

12–15 min core + cameos. Every beat is a fresh one-liner — skippable without state damage. If
the build is unavailable, Beat 2's exact term and the guard-oracle outputs can be narrated from
the committed tests, and the Dovetail-only build's typed fail-closed error is itself
demonstrable.

Recording: piped stdin works — `printf '…\n…\n' | target/release/repl rholang` replays the whole
script non-interactively (rustyline detects the non-tty and reads lines directly), which is how
the CI gate drives it. For a recording that shows the typing, drive a tmux pane
(`tmux send-keys`) captured with `asciinema rec` (plus `script` as backup). Either way the
recording matches the gate, because the gate runs these exact lines.
