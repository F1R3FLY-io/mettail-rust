# The Guarded Settlement Desk — RhoCalc `where` guards dispatching on F1r3node RSpace

A live REPL demonstration of semantic predicates (`where` clauses) in RhoCalc and of RhoCalc
applications dispatching via the rho-native integration onto F1r3node's RSpace. Stock RhoCalc —
no custom language definition. Every `exec` runs on a fresh in-memory Rho machine; the `step`
trace observes the production tuplespace one committed COMM at a time under a fixed seed, so a
recording and a live run match on trace content.

> Status: outputs marked **(to validate)** are pinned during the script-validation build window
> (prep item P3 below) before presenting. Guard-spelling fallbacks are inline per beat.

Launch (binary/CLI name validated in P3; the repl package takes a startup language):

```
$ target/release/repl rhocalc
```

Load the desk bindings (or paste the two definitions from `settlement.env` manually):

```
RhoCalc> load-env demos/rhocalc-settlement/settlement.env
```

---

## Beat 0 — Orientation (30 s)

```
RhoCalc> info
```

Expected **(to validate)**: the RUNTIME section names the two-stage Dovetail+Rholang backend.

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

Expected: `OUT: [BigInt(0x03)] (1 value(s))` — bare RhoCalc literals are arbitrary-precision;
the raw big-int bytes are what rests on the tuplespace.

**Proves**: the host computes nothing (the A-S4 lowering purity result); the value is produced by
the machine's metered `EPlus` and read back off RSpace (the `@("OUT")!(v)` wrap).

> "One plus two never runs on my laptop's CPU path — it lowers to the machine's metered
> expression algebra, and what you see is literally the bytes resting on the tuplespace."

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
(Parse fallback if `<=` collides with the persistent-bind reading: use `where px < 46u32` —
the machine path is ELte/ELt either way.)

```
RhoCalc> exec { desk | @("offer")!(55u32) }
```

Expected: `OUT: [] (0 value(s))` — the veto is VISIBLE as an empty observation channel.

```
RhoCalc> exec { desk | @("offer")!(55u32) | @("offer")!(42u32) }
```

Expected: `OUT: [42] (1 value(s))` — the 55 offer is never consumed; it stays on the book.

**Proves**: the `where` clause rides as `Receive.condition`; the machine matcher's
`check_commit` evaluates it purely — COMM-free — and a failed guard leaves the consume
uncommitted and the datum resting. Fail-closed veto, zero partial effects.

> "The guard is not an if-statement in the body — the body never starts. The veto happens inside
> the machine's matcher, before the COMM commits, and the rejected offer is still on the book
> for anyone else."

## Beat 4 — Atomic cross-channel settlement (2 min)

```
RhoCalc> exec { settle | @("bid")!(42u32) | @("ask")!(10u32) }
```

Expected: `OUT: [420] (1 value(s))` — both legs consumed atomically; the product computed by the
machine's `EMult`.
(Parse fallback if infix `*` in the guard trips the drop-prefix reading: use a budget guard
`where px + qty < 60u32` — guard-internal `+` and `*` are equally supported.)

```
RhoCalc> exec { settle | @("bid")!(60u32) | @("ask")!(10u32) }
```

Expected: `OUT: [] (0 value(s))` — 600 > 500: BOTH the bid and the ask remain resting.

**Proves**: multi-channel join + cross-bind guard evaluated once over the combined bindings —
all-or-nothing settlement.

> "Two channels, one atomic rendezvous. The guard sees both legs at once; if the trade violates
> the budget, neither leg is consumed. That is transactional matching as a language primitive."

## Beat 5 — SafeArith as a veto: division by zero cannot settle (1.5 min)

```
RhoCalc> exec { for(@q <- @("qty") where 100u32 / q >= 1u32){@("OUT")!(q)} | @("qty")!(0u32) }
```

Expected: `OUT: [] (0 value(s))` — no crash, no wrap: `DivisionByZero` inside the pure guard
evaluator is a guard-fail.

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

Expected **(to validate)**: `N reduction step(s) on the Rho machine`, a
`[Rho COMM] COMM[…] "offer" ⇐ {42} ▸ cont …` node, then `apply 0` advances to
`[Rho output] OUT observes 42` and quiescence.

```
RhoCalc> step { desk | @("offer")!(55u32) }
```

Expected **(to validate)**: ZERO committed COMMs (the router falls back to the Layer-1 graph:
"No rewrites from this term") — the veto is provably COMM-free: a live tracer recording every
committed COMM on real RSpace saw none.

**Proves**: the Layer-2 stepper wraps the real f1r3node RSpace (one committed COMM per step,
deterministic seed); guard evaluation emitted no COMM.

> "This trace isn't a simulation — it's an observer bolted onto the production tuplespace,
> releasing one committed COMM per keypress. And when the guard vetoes, the recorder is empty:
> the predicate ran without a single COMM."

## Beat 7 — The universal mandate, fail-closed (1 min)

```
RhoCalc> exec [1, 2].length()
```

Expected: a typed error — "RhoCalc term could not be lowered to the Rho machine (A-S4
fail-closed lowering; no host fold-normalization fallback): … list method".

> "No silent host fallback exists anymore. Either it runs on the machine, or you get a typed
> refusal naming the construct."

## Optional cameo A — the τ machinery (1 min)

```
RhoCalc> lang lambda
Lambda> step --taus (lam x. x, lam a. lam b. a)
```

Expected **(to validate)**: `[τ drive]`/`[τ subst]` steps — the reduction machinery itself is
COMMs (the driver dispatch, the substitution TRS, the fired-rule ledger writes).

## Optional cameo B — the only non-machine site (1 min)

```
Lambda> lang calculator
Calculator> exec 5 / 0
```

Expected: `backend: Dovetail`, `artifact: DovetailRunReport` — a semantic-predicate deferral
lazily building the report: today's only non-Rho-machine runtime site, the operational face of
INV-14.

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

## Prep status

- **P1 (this directory)**: DONE — `settlement.env` + this run sheet.
- **P2 (queued)**: RhoCalc-level `where`-guard exec tests in `rho_rhocalc_ast.rs` (single-bind
  pass/veto; cross-bind veto leaves both; `/0`-guard veto) — closes the one validated gap (no
  end-to-end RhoCalc-`where`-through-the-machine test exists yet) and doubles as script
  validation.
- **P3 (build window)**: run this script verbatim; pin every (to validate) output; confirm the
  `<=` and infix-`*` guard parses (fallbacks inline above); confirm piped-stdin/rustyline for
  recording.
- **Optional polish (not prerequisites)**: decimal rendering for BigInt observations
  (display-only); a consumed-cost readout in exec output (future work — metering runs, the REPL
  just doesn't print the number today; claim metering via the tests/source above).

## Logistics

12–15 min core + cameos. Every beat is a fresh one-liner — skippable without state damage. If
the build is unavailable, Beat 2's exact term and the guard-oracle outputs can be narrated from
the committed tests, and the Dovetail-only build's typed fail-closed error is itself
demonstrable. Recording: validate rustyline-vs-piped-stdin; else drive a tmux pane
(`tmux send-keys`) captured with `asciinema rec` (plus `script` as backup), recorded during the
P3 window so the recording IS the validated run.
