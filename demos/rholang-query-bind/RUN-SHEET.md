# The Query Bind — a request, a private return channel, and a reply, in one round trip

## The claim, in one sentence

> `!?` is Rholang's request/response sugar: one row of a `for` mints a **private** return
> channel, ships it to a service with the request's arguments, and binds whatever the service
> replies on it — and every value this page prints is one the **f1r3node reducer computed**
> during that round trip.

> Status: **VALIDATED end to end, 2026-07-28.** Every command below was run against a freshly
> built binary. Beats 1, 3 and 4 are byte-identical over 8 consecutive runs and over scheduler
> widths 1, 2, 8 and 32; beat 4's five-observation sibling — beat 2 — has a byte-identical
> observation *set* over 12 runs and the same four widths (see
> [Reading a multiset](#reading-a-multiset)).

> ⚠ **This feature did nothing until 2026-07-28.** Not "did the wrong thing" — *nothing*. The
> expansion was computed and then discarded, so the program that ran still held the raw query
> row, the lowering read the service channel as an ordinary receive channel, dropped the
> arguments, and emitted **no request send at all** (`ac7f71af`; a second defect in the
> expansion's `Par` ordering followed in `6e6639ee`). A receive with no partner is *supposed*
> to rest, so the failure raised nothing, printed nothing, and exited zero. That is why every
> beat below carries a control, and why the run sheet keeps saying so.

## Setup — before the audience arrives

```
cargo build -p rholang-runtime --bin rholang --features "rholang-runtime lambda-runtime calculator-runtime"
```

The `rholang` bin target requires all three features. Run every command from the workspace
root; each completes in well under a second.

**No stack incantation.** Nothing on this page needs `RUST_MIN_STACK`, and
`no_run_sheet_command_line_raises_the_stack` asserts that no command line carries one.

## The operator

```
for(p <- svc!?(a, b)) { B }   ≡   new r in { svc!(*r, a, b) | for(p <- r) { B } }
```

Three things happen, in this order:

1. **`new r`** mints a name nothing else in the program can spell.
2. **`svc!(*r, a, b)`** sends the request — the return channel **first**, then the arguments.
3. **`for(p <- r)`** receives the reply on that private channel and runs `B`.

The **send** is the leg that was missing. Without it, step 3 waits on a channel nobody sends to,
which is indistinguishable — in output, in exit code, and in log volume — from a service that
chose not to answer.

---

## ★ How to read these beats — the discipline, stated once

Every program on this page obeys four rules, and each rule closes off one way a demo of this
feature could look convincing while proving nothing:

| rule | the reading it refutes |
|---|---|
| **A control fires in the same file and the same run** — an ordinary send/receive pair publishing a greeting | "the harness cannot see `@"OUT"` at all" |
| **No desk publishes to `@"OUT"` itself** — every desk replies on the return channel that arrived | "the observation was reachable without the private channel" |
| **Every desk pins its arguments by pattern** (`for(@reply, @cents <- @"quote")`) | "the request travelled without its arguments" |
| **Every published number is arithmetic the reducer performed** — no answer appears in any program | "the answer was transcribed" |

The gate (`rholang-runtime/tests/query_bind_demo.rs`) asserts all four, and asserts one thing
more: with the `!?` deleted from beat 1 — the service channel left in place, so the row becomes
an ordinary receive — the run publishes **only** the greeting. The demo can fail, in the
direction that matters.

<a id="reading-a-multiset"></a>
### Reading a multiset

`@"OUT"` is a **multiset**, not a log. The interpreter prints what rests on it when the program
comes to rest, and independent branches race to publish, so the `[0]`/`[1]`/… **indices are not
stable** when more than one branch publishes independently. **Read the values, not the numbers.**

Beats 1, 3 and 4 publish along a single causal chain — the control's continuation opens the desk,
and each beat settles into exactly **one** further datum — so their transcripts *are* byte-exact.
Beat 2 runs four independent surfaces on purpose, so its five lines arrive in whatever order the
reducer produced them. Its *set* is invariant: byte-identical over 12 runs and over
`TOKIO_WORKER_THREADS` ∈ {1, 2, 8, 32}.

---

## Beat 1 — the round trip (2 min — start here)

```
$ target/debug/rholang demos/rholang-query-bind/01-round-trip.rho
```
```
  @"OUT" observations (2):
    [0] ⟦42⟧
    [1] ⟦"the desk is open"⟧
```

Three rows ran. **Point at how many printed.**

| row | what it is | printed |
|---|---|---|
| the **control** | an ordinary `@"open"!(…)` / `for(@greeting <- @"open")` pair | `"the desk is open"` |
| the **query** | `for(price <- @"quote"!?(14)) { @"OUT"!(*price) }` | `42` |
| the **closed desk** | `for(unanswered <- @"closed"!?(14)) { … }` — nothing serves `@"closed"` | *nothing* |

Read it as a triple. **Two observations and no third is the pass.** One observation means the
round trip did not happen. Three would mean a query answered itself.

`42` is `14 * 3`, performed by the reducer at reply time. `cat` the file: the numeral `42`
appears in the header comment and nowhere in the program.

> Say: **"One line asked a question of a service, on a channel the service could not have known
> in advance, and the answer came back."**

---

## Beat 2 — every surface the grammar declares (3 min)

```
$ target/debug/rholang demos/rholang-query-bind/02-every-surface.rho
```
```
  @"OUT" observations (5):
    [0] ⟦"the empty reply arrived"⟧
    [1] ⟦54⟧
    [2] ⟦42⟧
    [3] ⟦169⟧
    [4] ⟦"four surfaces, one desk"⟧
```

⚠ One observed order, of five. The indices move between runs; the five values do not.

`!?` is not one rule. The grammar declares **three** `InputBind` rules whose syntax carries
`!?(`, and the argument list adds an arity axis:

| rule | written | the reply binds | this run |
|---|---|---|---|
| `InputBindQuery` | `for(p <- svc!?(a…))` | a **name** — the body writes `*p` | `42` = `20 + 22` |
| `InputBindQuotedQuery` | `for(@q <- svc!?(a…))` | a **process** — used directly | `54` = `6 * 9` |
| `InputBindEmptyQuery` | `for(<- svc!?(a…))` | **nothing** — the body running *is* the reply | `"the empty reply arrived"` |
| *(arity)* | `svc!?()` — no arguments | a **name**; the request is **monadic** | `169` = `13 * 13` |

The zero-argument row is its own axis because `svc!?()` must expand to `svc!(*r)` — a *monadic*
send whose datum is `⟦*r⟧` — so the ordinary responder `for(@reply <- @"square")` matches it. A
wrapper that made the datum `⟦[*r]⟧` instead would need `for(@[reply] <- …)`, and this row is
what would rest.

**Why all four are in one file.** The quoted form stayed inert *after* the first fix landed: the
rewriter handled the plain and empty forms and fell through on the quoted one, while the guard
that was supposed to report the omission omitted it from all four of its arms. A demo showing one
surface would have looked identical. The gate reads the covered set **off the grammar metadata**,
so a fourth `!?` rule fails the build until this beat shows it.

**The empty surface is the one honest exception to "every value is computed."** Nothing is bound,
so nothing *can* be computed from the reply; the observation is that the body ran, which happens
only when the empty message lands on the private return channel. Its marker is therefore a
string — the only published value in this directory that is not arithmetic.

---

## Beat 3 — two queries, one `for`, two private channels (3 min — the point)

```
$ target/debug/rholang demos/rholang-query-bind/03-two-desks.rho
```
```
  @"OUT" observations (2):
    [0] ⟦[50, 1000, 1050]⟧
    [1] ⟦"two desks, one join"⟧
```

Two `!?` rows joined by `&` in **one** `for`. The expansion hoists both requests under a single
`new` with **two** binders:

```
new r1, r2 in {
  @"fee"!(*r1, 500) | @"tax"!(*r2, 500) |
  for(@fee <- r1 & @tax <- r2) { … }
}
```

**One return channel per row is a claim about pairing, and pairing is invisible when both
services answer alike.** So the two desks are given the *same* request argument and reply
differently:

| desk | request | replies with | value |
|---|---|---|---|
| `@"fee"` | `500` | `cents / 10` | `50` |
| `@"tax"` | `500` | `cents * 2` | `1000` |

and the body publishes both **in row order, inside one list**. The *positions* are the evidence:
`[50, 1000, …]` says the fee row received the fee desk's reply. If the two rows shared a return
channel, either reply could satisfy either row and `[1000, 50, …]` would be equally admissible.

The third element, `1050`, is summed by the reducer **after** the join, so it exists only if both
round trips completed. None of `50`, `1000`, `1050` appears in the program.

> Say: **"Two questions, two private mailboxes, one atomic answer — and the order in the list is
> the proof that the mail was not crossed."**

Publishing one list rather than three sends is also why this transcript is byte-exact: three
sends would rest three data on a multiset channel.

---

## Beat 4 — the sugar *is* its expansion (2 min)

```
$ target/debug/rholang demos/rholang-query-bind/04-sugar-is-its-expansion.rho
```
```
  @"OUT" observations (2):
    [0] ⟦[49, 49, true]⟧
    [1] ⟦"asked twice, of one desk"⟧
```

One desk — `for(@reply, @side <= @"area") { @reply!(side * side) }`, **persistent**, so it serves
both callers — is asked the same question twice in the same run:

| route | written | who mints the return channel |
|---|---|---|
| the **sugar** | `for(sugar <- @"area"!?(7)) { … }` | the expansion |
| the **expansion** | `new manual in { @"area"!(*manual, 7) \| for(@byhand <- manual) { … } }` | the program, by hand |

and the two answers are compared **by the reducer**: the list's third element is
`*sugar == byhand`, an equality the machine evaluates over the two values it is actually holding.
`⟦true⟧` is a computed verdict, not a claim on this page.

**Why this beat exists.** The defect was that the right program was *built and then not used*. So
"the sugar expands correctly" and "the expansion is what runs" are two different claims, and only
the second is about the running program. Here the hand-written expansion sits in the source beside
the sugar, reaching the same desk; if `!?` lowered to anything else, the two values would have to
agree by coincidence.

The beat can fail visibly: an undecidable comparison publishes nothing, a false one publishes
`false`.

---

## What this rests on

- **The values are computed.** `42`, `54`, `169`, `50`, `1000`, `1050`, `49` appear in no program
  on this page; only their operands do.
- **The private channel is load-bearing.** No desk writes to `@"OUT"`; every observation required
  the request send, the reply on the minted channel, and the query row's own receive firing.
- **The arguments travelled.** Every desk pins them by pattern, so a reply witnesses them.
- **Silence is refutable.** Beat 1's closed desk rests while the control fires, in the same run.
- **The demo can fail.** Delete the `!?` from beat 1 and the `42` disappears; the gate asserts it.

## Scope — what this does not show

`!?` is **request/response over one reply**, not a session type. The private channel is used once
per query; a service that wanted to stream would send a channel of its own in the reply. Nothing
here constrains the service to answer — beat 1's closed desk is exactly that case, and it rests.

## If something goes wrong live

| symptom | cause | fix |
|---|---|---|
| only the greeting prints | the query row did not complete a round trip — this is the pre-`ac7f71af` symptom exactly | rebuild; the fix landed 2026-07-28 |
| nothing prints at all | the binary is stale, or the program failed to parse | rebuild with the setup line; a parse error exits `65` and says so |
| the indices differ from this page | expected in beat 2 — `@"OUT"` is a multiset | read the values, not the numbers |

## Files

| | |
|---|---|
| `01-round-trip.rho` | one service, one query, one reply — with a control and a closed desk |
| `02-every-surface.rho` | all three declared `!?` rules, plus the zero-argument arity |
| `03-two-desks.rho` | two query rows in one `for`, paired by row order |
| `04-sugar-is-its-expansion.rho` | the sugar and the hand-written expansion, compared by the reducer |

The gate is `rholang-runtime/tests/query_bind_demo.rs`; the feature's own behavioural suite is
`rholang-runtime/tests/rholang_query_bind.rs` (16 cells, landed with `ac7f71af`).
