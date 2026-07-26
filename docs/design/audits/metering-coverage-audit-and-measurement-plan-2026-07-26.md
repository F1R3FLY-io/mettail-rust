# Metering Coverage — Audit and Measurement Plan (2026-07-26)

**Status.** Read-derived audit plus an executable measurement plan. **Nothing in
this document was measured.** Every quantitative claim is either (a) copied from
a source comment that itself claims to be measured — labelled *S-cited* — or (b)
an experiment specified here for someone else to run. See [§8](#8-evidence-ledger)
for the per-claim provenance ledger.

**Why it exists.** The governing directive is:

> Integrate with `../f1r3node-rust-mettail/` to ensure the operations are
> properly metered by cost accounting. Do not reproduce cost accounting and
> metering within mettail-rust.
>
> — and the principle behind it: *evaluations must be metered, so speculated
> evaluations without metering is the DoS surface.*

Those two rules compose rather than conflict: every evaluation must be charged,
and the charging must live on the F1r3node side of the seam. Budgets are
F1r3node's, sourced from `wallet.txt`. This document establishes **where
evaluation happens today and whether a charge reaches it**, and specifies how to
prove each answer by measurement.

**Scope fence — the semantic-predicate lane is documented, not designed.** By
the standing definition, *if it is in a `where` clause, it is a semantic
predicate*. A metering design for semantic predicates is being prepared
separately by Greg. Sections [§3](#3-the-semantic-predicate-guard-lane-documented-not-designed),
[§5](#5-scaling-questions-for-the-guard-lane-to-be-measured) and
[§6](#6-the-constraint-that-complicates-any-guard-metering-design) therefore
**describe and quantify**; they propose no charge, no charge table, and no
budget. Anything ambiguous about whether a site sits inside that lane is treated
as inside and reported rather than acted on.

**Diagram convention.** This suite (`docs/design/audits/`) has no PlantUML figure
pipeline and no `validate.sh`; diagrams here are inline unicode box-drawing, as
the surrounding audit documents and the cited source headers use. Mathematical
expressions use GitHub-flavored math delimiters.

---

## Table of contents

1. [Executive summary](#1-executive-summary)
2. [How charging actually works in this tree](#2-how-charging-actually-works-in-this-tree)
3. [The semantic-predicate guard lane (documented, not designed)](#3-the-semantic-predicate-guard-lane-documented-not-designed)
4. [The non-guard sites](#4-the-non-guard-sites)
5. [Scaling questions for the guard lane (to be measured)](#5-scaling-questions-for-the-guard-lane-to-be-measured)
6. [The constraint that complicates any guard metering design](#6-the-constraint-that-complicates-any-guard-metering-design)
7. [The measurement plan](#7-the-measurement-plan)
8. [Evidence ledger](#8-evidence-ledger)
9. [Seam inventory — where a charge could be levied](#9-seam-inventory--where-a-charge-could-be-levied)

---

## 1. Executive summary

### 1.1 The direct answer

**Yes — the substrate guard lane is unmetered today, and so is f1r3node's own
guard lane.** A `where`-clause guard is evaluated with **no cost handle in
scope**, on both deciders, and the number of evaluations is program-controlled.
This is established structurally (the decider types hold no budget, and the
trait method's signature admits none), not by measurement; [§7.3](#73-m1--the-guard-lane-zero)
specifies the measurement that would confirm it.

The finding is **broader than mettail**. The identical gap exists on f1r3node's
own consensus path, reachable from ordinary Rholang source, with no mettail
component involved — see [§3.2](#32-the-same-gap-exists-on-f1r3nodes-consensus-path).

### 1.2 Two corrections to widely-repeated facts

Both were relayed into this task as premises and both are **wrong in this tree**.
They matter because each one, if believed, invalidates the measurement.

| # | Relayed premise | Reality | Evidence |
|---|---|---|---|
| C1 | "`create_rho_runtime` already wires `ChargingRSpace`/`CostManager`." | **Neither type exists.** `grep` over the whole f1r3node tree returns zero definitions of either. `CostManager` survives only inside one assertion *string* in a test. The real mechanism is `RuntimeBudget` + `MeteredMachine` + the `HasCost` trait. | `rholang/src/rust/interpreter/accounting/has_cost.rs:5-7`; `rholang/src/rust/interpreter/metering.rs:96-155`; `rholang/tests/concurrent_rspace_architecture_repro_spec.rs:69` (the string) |
| C2 | "Under `Cost::unsafe_max()` metering is OFF / unbounded." | **Metering stays ON.** `cost().set(…)` routes to `reset_from_token`, which writes `initial_tokens` and never touches the `unmetered` flag. Charges are still recorded and `total_cost()` still counts them. What `unsafe_max` disables is only the *out-of-phlogiston boundary*. | `accounting/mod.rs:944-947` (`set`), `:955-990` (`reset_from_token`, no `unmetered` write), `:102/:365/:378-380/:1196-1204/:1207-1208` (every site that does touch the flag) |

C2 is the one that makes this whole audit tractable: because mettail's runtime is
built from `CostAccounting::empty_cost()` — the **metered** constructor
(`accounting/cost_accounting.rs:16`, versus `unmetered_cost()` at `:18`) — and
because `unsafe_max` does not flip the flag, **`runtime.cost().total_cost()` is a
live instrument inside mettail's own runtime, with no budget changes required.**

Had C2 been true, `total_cost()` would return a hard-coded `0`
(`accounting/mod.rs:1228-1230`) and every "the cost did not move" reading would
have been a false positive. That is precisely the trap the teeth test in
[§7.2](#72-t0--the-teeth-test-mandatory-gate) exists to catch, and it is why no
zero in this plan may be trusted before T0 passes.

### 1.3 Site table, ordered by severity

Severity is driven by whether the work is **program-controlled** (an attacker
chooses its magnitude) or bounded by construction.

| # | Site | What is evaluated | Charged? | Cost handle reachable? | Production path? | Program-controlled? | Severity |
|---|---|---|---|---|---|---|---|
| **S1** | `SubstrateGuardMatcher::check_commit` → `substrate_guard_verdict` (`rholang-runtime/src/guard_par_substrate.rs:721`, `:826`) | Substitution over the guard `Par`, guard encoding, Presburger/SFT decision, plus `rho_pure_eval` on each opaque fragment | **No** | **No** — decider is `SubstrateGuardMatcher { spatial: Matcher }`, both unit-sized, no budget field; `Match::check_commit`'s signature carries none (`rspace++/src/rspace/match.rs:30`) | mettail `exec`/`step`/speculation | **Yes** — guard complexity × candidate enumeration | ★★★ (guard lane — Greg's) |
| **S2** | f1r3node `Matcher::check_commit` → `guard_passes` (`rholang/src/rust/interpreter/matcher/match.rs:79`, `:141`) | `rho_pure_eval::eval_with` over the whole guard, with the spatial-match oracle | **No** | **No** — `pub struct Matcher;` is a field-less unit struct (`:14`) | **f1r3node consensus path**, from Rholang source | **Yes** — same shape | ★★★ (guard lane — Greg's) |
| **S3** | `Cost::unsafe_max()` in mettail drivers (`rholang-runtime/src/run.rs:542`, `step.rs:642`) | Nothing itself; it removes the OOP *boundary* while leaving accounting live (C2) | Accounting **yes**, enforcement **no** | Yes — `runtime.cost()` is in scope at both sites | mettail `exec`/`step` (in-memory, not a deploy boundary) | Bound only | ★★ |
| **S4** | Tier-3 held-fold body (`rholang-runtime/src/fold_contract.rs:212-241`, `fold_eval` `:144`) | Host-side Rust arithmetic on one ground operand | **No** for the body | **No** — `ProcessContext` has no cost field (`system_processes.rs:206-213`); nor does `ContractCall` (`contract_call.rs:30-33`) | mettail exec, for fold-bearing terms | Per-call magnitude bounded except for the BigInt/BigRat arms; **call count is gated behind charged COMMs** | ★★ |
| **S5** | Compile-time guard discharge (`rholang-runtime/src/guard_discharge.rs`) | Substrate verdict + `rho_pure_eval` at lowering | N/A — not on the deploy path | N/A | Compiler, not runtime | Yes, but pre-deploy | ★ (cost-determinism note, not a gap) |
| **S6** | Speculation sandbox (`rholang-runtime/src/speculation.rs:741-809`) | Whatever the speculated program does | **Yes, by construction** | Yes — `fund_from` resets from the host's remaining token (`:802-809`) | Stage 1 in flight (another agent) | Bounded by the host deploy | ✓ (already fail-shut) |

**S6 is the model the other sites are measured against.** It is the only site in
the table that has already solved the problem, and it solved it without a new
consensus parameter: the sandbox is created with a **zero** budget and can only
be funded from the host's remaining phlogiston, so an unmetered speculative
evaluation is *unrepresentable* rather than merely discouraged
(`speculation.rs:762-770`). This audit confirms the mechanism that Stage 1 needs
exists and is wired; see [§4.4](#44-s6--the-speculation-sandbox-confirmed-present).

---

## 2. How charging actually works in this tree

### 2.1 The mechanism map

```text
   ┌──────────────────────────────────────────────────────────────────────┐
   │ RuntimeBudget            accounting/mod.rs                           │
   │   initial_tokens : AtomicU64      consumed_tokens : AtomicU64        │
   │   unmetered      : AtomicU64   ◀── ONLY set by unmetered() / :378    │
   │                                    set_unmetered() / :1196           │
   │                                    enter_unmetered_scope() / :1207   │
   │   get()      :935  → initial − consumed   (unsafe_max if unmetered)  │
   │   total_cost():1227 → reconciled consumed (0        if unmetered)    │
   │   set(c)     :944  → reset_from_token(…)  ◀── does NOT touch the flag│
   └───────────────────────────────┬──────────────────────────────────────┘
                                   │ HasCost::cost() → &RuntimeBudget
                                   │ has_cost.rs:5-7
                    ┌──────────────┴───────────────┐
                    ▼                              ▼
   ┌────────────────────────────────┐   ┌─────────────────────────────────┐
   │ MeteredMachine  metering.rs    │   │ RhoRuntimeImpl.cost             │
   │  reserve_comm            :96   │   │  rho_runtime.rs:250, :452       │
   │  reserve_reduction       :129  │   │  built from                     │
   │  reserve_primitive       :133  │   │  CostAccounting::empty_cost()   │
   │  reserve_incremental_…   :138  │   │  rho_runtime.rs:1255            │
   │  reserve_substitution    :153  │   │  ⇒ METERED (flag = 0)           │
   └────────────────┬───────────────┘   └─────────────────────────────────┘
                    │  held by the reducer only (rho_runtime.rs:1084)
                    ▼
   ┌──────────────────────────────────────────────────────────────────────┐
   │ Reduce (reduce.rs)   ── the ONLY component holding a cost handle     │
   └──────────────────────────────────────────────────────────────────────┘
                    │
                    │  hands a TaggedContinuation{ guard } to consume
                    ▼
   ┌──────────────────────────────────────────────────────────────────────┐
   │ rspace++  space_matcher.rs  ── NO cost handle anywhere below here    │
   │   search_candidate_selection :387                                    │
   │     leaf ⇒ matcher.check_commit(continuation, &matched)  :401        │
   └──────────────────────────────────────────────────────────────────────┘
                    │
                    ▼   Match trait object — chosen by whoever built the RSpace
        ┌───────────┴────────────┐
        ▼                        ▼
  Matcher (f1r3node)      SubstrateGuardMatcher (mettail)
  match.rs:14             guard_par_substrate.rs:692
  `pub struct Matcher;`   `{ spatial: Matcher }`
  ── no fields            ── no fields beyond a field-less Matcher
```

The diagram states the structural result: **the cost handle stops at the
reducer.** Everything below the `consume` call — the candidate search, the
spatial matcher, and the commit guard — runs in `rspace++`, a crate that sits
*below* `rholang` in the dependency order and has no access to
`RuntimeBudget` at all. `Match::check_commit`'s signature
(`rspace++/src/rspace/match.rs:30`) is

```rust
fn check_commit(&self, _k: &K, _matched: &[&A]) -> bool { true }
```

— `&self`, a continuation, the matched payloads, and a `bool` out. There is no
parameter through which a budget could arrive, and neither implementing type has
a field that could carry one. That is the whole of the reachability argument, and
it is a compile-time fact rather than an empirical one.

### 2.2 What *is* charged around a guarded receive

This is the part most easily misread as "guards are metered". Three charges fire
per guarded receive, and none of them is the guard's evaluation:

| Charge | Site | Magnitude | Fires |
|---|---|---|---|
| `reserve_comm(receive_eval_cost())` | `reduce.rs:1563` | 11 (`costs.rs:328`); consensus counts the COMM as 1 unit regardless | Once per receive evaluation |
| `substitute_and_charge(guard, 1, env)` | `reduce.rs:1571-1575` | Proportional to the **serialized size of the guard term** | Once per receive evaluation |
| `substitute_and_charge(pattern, 1, env)` per bind | `reduce.rs:1587` | Proportional to pattern size | Once per bind |

So the guard is charged **once, for its size, at installation time.** It is then
evaluated an unbounded number of times, at commit time, for free. Writing that
as a formula, with `$`G`$` the guard's size, `$`E(G)`$` the cost of evaluating it once,
and `$`N`$` the number of complete candidate selections the search reaches:

```math
\text{charged} \;=\; \Theta(G) \qquad\text{while}\qquad \text{performed} \;=\; \Theta\bigl(G\bigr) \;+\; N \cdot E(G)
```

`$`N`$` is program-controlled, and `$`N`$` does not appear on the left. That gap —
not the constant factor — is the DoS shape the directive names.

---

## 3. The semantic-predicate guard lane (documented, not designed)

> **Scope fence.** This section records current state and quantifies the work. It
> proposes nothing. Charge design for semantic predicates is Greg's.

### 3.1 What actually happens per decision

`check_commit` is consulted **once per complete candidate selection**, at the
leaf of the depth-first search over binds
(`rspace++/src/rspace/space_matcher.rs:396-405`; the source calls it "the ONE
place a commit guard is consulted on a candidate selection"). Both deciders then
do the following work, per call:

**f1r3node's `Matcher` (`matcher/match.rs:79-91` → `guard_passes` `:141-167`):**

1. Concatenate every bind's bound `Par`s into one `Vec<Par>` (`:86-89`).
2. Build a `rho_pure_eval::Env` by cloning each bound `Par` into it (`:142-145`)
   — a **deep clone per bound value, per candidate**.
3. `rho_pure_eval::eval_with(condition, &env, &SpatialMatcherOracle)` (`:146`)
   — a full evaluation of the guard term. Each `EMatchesBody` inside it
   constructs a fresh `SpatialMatcherContext` and clones both target and pattern
   (`:124-127`).
4. Collapse the result: non-`GBool`, `false`, and evaluation error are one
   verdict (`:147-166`).

**mettail's `SubstrateGuardMatcher` (`guard_par_substrate.rs:721-734` →
`substrate_guard_passes` `:749` → `substrate_guard_verdict` `:826-856`):**

1. Same concatenation (`:728-732`), with the destination pre-sized.
2. `substitute_bound_pars(condition, bound_pars)` — one substitution pass over
   the guard `Par` (`:827`).
3. `encode_par_guard(&substituted)` — one encoding pass producing a formula plus
   a set of opaque fragments (`:828`).
4. Refuse if any variable survived substitution (`:831-836`).
5. For **each** opaque fragment, call `guard_discharge::machine_verdict`, which
   is itself a `rho_pure_eval` run (`:840-846`).
6. `ground_verdict_with(…, CONSENSUS_SUBSTRATE_CONFIG, …)` — the Presburger/SFT
   decision (`:849-855`).

Both are `$`\Theta(G)`$`-ish per call with a non-trivial constant (clones,
substitution, encoding, and one or more evaluator runs). Neither consults a
budget at any step.

### 3.2 The same gap exists on f1r3node's consensus path

This is the finding with the widest blast radius, and it involves no mettail
code. The Rholang **surface normalizer** populates `Receive.condition` from a
source-level `where` clause:

- `compiler/normalizer/processes/p_input_normalizer.rs:489-507` — "Optional
  `where`-clause guard", reading `receipts[0].guard`;
- `:526` — `let guard_par = guard_result.as_ref().map(|gr| gr.par.clone());`
- `:563` — `condition: guard_par,` on the constructed `Receive`.

A populated `Receive.condition` is exactly what `check_commit` reads. So an
ordinary Rholang deploy carrying `for (…) where <guard> { … }` reaches f1r3node's
own `Matcher::check_commit` → `guard_passes` → `rho_pure_eval::eval_with`, with
no cost handle in scope, on a validator.

**Unverified, and load-bearing for severity:** whether that surface syntax is
accepted end-to-end from a *signed deploy* on the current grammar, and whether
any deployed program uses it. The normalizer arm exists and is wired; that is
what has been read. [§7.6](#76-m4--on-chain-reachability-of-the-surface-where-guard)
specifies the experiment. Until it runs, treat the on-chain exposure as
**present in code, unconfirmed in reach**.

### 3.3 The compile-time leg differs, and differs in the right direction

Compile-time discharge (`rholang-runtime/src/guard_discharge.rs`) runs the same
substrate but has a **different cost profile and a different risk profile**:

| | Compile-time leg (`guard_discharge::classify`) | Run-time leg (`check_commit`) |
|---|---|---|
| When | Once, at lowering | Once per complete candidate selection |
| Multiplicity | 1 per guard site | `$`N`$` per guard site, `$`N`$` program-controlled |
| Who pays | The compiler operator's wall clock | The validator's wall clock, per COMM attempt |
| Budget domain | Bounded, `$`2^{w}`$` — hence the machine-verdict soundness fence (`guard_discharge.rs:56-70`) | Quantifier-free after substitution, so answers are about `$`\mathbb{Z}`$` (`guard_par_substrate.rs:820-825`) |
| Consensus exposure | Indirect — changes which artifact bytes are emitted | Direct — decides which COMMs fire |

The compile-time leg **removes** run-time work when it discharges: a discharged
guard is recorded by *omitting* `Receive.condition`, after which `check_commit`
returns `true` on its first line with no work at all
(`guard_discharge.rs:10-13`, `:127-131`). Discharge is therefore the one existing
mechanism that reduces the unmetered run-time surface, and its yield is a
relevant input to any charge sizing.

One consequence is already recorded in-tree and is worth surfacing here because
it is consensus-visible: discharging skips one `substitute_and_charge` per
receive-eval, so **a program's phlogiston price depends on the compiler version
that produced its artifact** (`guard_discharge.rs:105-111`). It is sound — every
validator replays the same fixed bytes and charges the same amount — but it means
"the cost of this program" is only well-defined relative to an artifact.

---

## 4. The non-guard sites

### 4.1 S3 — `Cost::unsafe_max()` in the mettail drivers

Two production sites, plus bench/experiment support:

| Site | Line | Character |
|---|---|---|
| `inj_on_runtime` | `rholang-runtime/src/run.rs:542` | The `exec` path's injection |
| step driver | `rholang-runtime/src/step.rs:642` | The `step` path's injection |
| `e6a_support` | `rholang-runtime/src/e6a_support.rs:1088` | Experiment harness |
| `bench_inj_and_read` | `rholang-runtime/src/bench_support.rs:973` | Benchmark |
| scion drive | `rholang-runtime/src/bench_support.rs:1382` | Benchmark |
| SA-vs-naive driver | `rholang-runtime/src/bin/bench_sa_vs_naive_driver.rs:1246` | Benchmark |

Given correction C2, the honest characterization is **not** "these paths are
unmetered". It is:

> These paths are **metered but unbounded**: charges accrue and `total_cost()`
> reports them, but the out-of-phlogiston boundary can never fire.

The historical justification — "the in-memory REPL runtime is not a deploy
boundary" — still holds for `run.rs` and `step.rs` as they stand: both build a
fresh `InMemoryStoreManager` per evaluation (`run.rs:503-507`), neither is
reachable from a validator, and neither settles anything on chain. It does
**not** hold for anything that speculates on behalf of an on-chain deploy, which
is why `speculation.rs` deliberately does the opposite (§4.4).

The measurable question is whether accrual is in fact live at these sites
([§7.4](#74-m2--accrual-under-unsafe_max)), because the whole audit's instrument
depends on it.

### 4.2 S4 — Tier-3 held-fold bodies

A held fold lowers to a contract call `@"<fold>"!(operand, *ret)` whose handler
is a host system-process `Definition` (`fold_contract.rs:202-242`). The handler
computes `fold_eval(operand, kind, width)` (`:232`, defined `:144-155`) and
`produce`s the result on the ack channel (`:235`).

**No cost handle is reachable in the handler.** `Definition::handler` receives a
`ProcessContext` (`system_processes.rs:252-263`), whose fields are `space`,
`dispatcher`, `block_data`, `invalid_blocks`, `deploy_data`, `system_processes`
(`:206-213`) — no budget. The `ContractCall` the handler builds carries only
`space` and `dispatcher` (`contract_call.rs:30-33`).

**But the exposure is materially smaller than S1/S2**, for a structural reason
worth stating precisely: the fold body cannot run without a COMM, and the COMM
*is* charged. Reaching the handler requires the lowered send and the lifted
`for(@r <- ret){…}` receive, both of which pass through the reducer and both of
which take `reserve_comm`. So

```math
\#\{\text{fold body executions}\} \;\le\; \#\{\text{charged COMMs}\}
```

The call count is therefore bounded by a metered quantity. What is *not* bounded
by a metered quantity is the **per-call magnitude** of the four fixed-width arms
versus the two arbitrary-precision arms: `FoldKind::Int/UInt/Float/Fixed` fold to
a fixed width and are `$`O(1)`$`, while `FoldKind::BigIntCast` and
`FoldKind::BigRatCast` (`fold_contract.rs:151-152`) are proportional to the
operand's magnitude. A single charged COMM can therefore carry an arbitrarily
large arbitrary-precision cast. That asymmetry is the part worth measuring
([§7.5](#75-m3--held-fold-body-cost-versus-comm-count)).

### 4.3 S5 — compile-time discharge

Not a metering gap: it runs in the compiler, before any deploy exists, and there
is no budget to charge against. Recorded here only for the cost-determinism
consequence in [§3.3](#33-the-compile-time-leg-differs-and-differs-in-the-right-direction).

### 4.4 S6 — the speculation sandbox (confirmed present)

The audit was asked to confirm that the mechanism Stage 1 needs exists and works,
and to flag anything that would prevent it. **It exists, and nothing found here
prevents it.**

```text
  host deploy budget ── RuntimeBudget (metered, real remaining balance)
        │
        │  fund_from(&host)                       speculation.rs:802-809
        │    available = host.remaining()                          :803
        │    sandbox.cost().reset_from_token(
        │        Token::coalesced(host.signature(), available))    :804-807
        ▼
  sandbox RhoRuntime ── created by create_rho_runtime with
                        CostAccounting::empty_cost()  ⇒ budget ZERO
                        and NO Cost::unsafe_max()     speculation.rs:762-770
        │
        │  run the speculation … sandbox accrues real charges
        ▼
  charge back: MeteredMachine::reserve_comm(sandbox.consumed())
               fails shut with OutOfPhlogistonsError if unaffordable
```

Three properties make this the right shape, and all three are readable in the
source:

1. **Fail-shut by construction.** The sandbox starts at zero, so an unfunded
   sandbox refuses to evaluate. Unmetered speculation is unrepresentable, not
   merely discouraged (`:764-768`).
2. **Same tokens, same lane.** Funding carries the host's *signature* as well as
   its remaining units (`:804-806`), so the spend is attributed to the same
   per-signature lane the deploy is.
3. **No new consensus parameter.** Metering *is* the bound: a runaway exploration
   exhausts the deploy and is rejected like any other over-budget program
   (`:795-798`).

Two facts this audit contributes to that work:

- **Correction C2 is what makes it coherent.** Because `set(unsafe_max)` does not
  disable accounting, `sandbox.consumed()` is meaningful, and the contrast the
  module draws with the `unsafe_max` drivers is a contrast about the *boundary*,
  not about accounting.
- **The sandbox inherits the S1 guard gap.** It is created with
  `SubstrateGuardMatcher` (`speculation.rs:749`), so guard evaluation inside a
  speculation is as unmetered as anywhere else. The charge-back bounds
  everything the *reducer* did; it does not bound what the *matcher* did. This is
  not a defect in Stage 1 — it is S1 showing up in one more place — but a design
  that assumes "charge back the difference captures the sandbox's whole cost"
  should know that the guard lane is outside that difference.

### 4.5 Residual Rust-side evaluation on admitted exec paths

Searched for and **not found** as a distinct site beyond S4. The earlier
campaigns that moved casts, folds and pre-normalization into the Rho machine
appear to have completed for the paths inspected here: the exec path builds a
`Par` and injects it (`run.rs:517-546`), and the remaining host-side computation
reached from an admitted exec path is the Tier-3 fold handler (S4) and the guard
deciders (S1/S2).

**This is a negative result from reading, over the crates inspected
(`rholang-runtime`, `fold_contract`, `guard_*`), not an exhaustive sweep.**
[§7.7](#77-m5--residual-host-side-evaluation-sweep) specifies how to make it
exhaustive and mechanically checkable.

---

## 5. Scaling questions for the guard lane (to be measured)

Stated as questions, with the analysis that makes them the right questions. None
of these has been measured here.

### 5.1 The DFS-leaf multiplication — why enumeration is the load-bearing input

The guard is asked once per **complete candidate selection**, not once per
receive. With `$`l`$` binds and pools `$`\text{pool}_0,\dots,\text{pool}_{l-1}`$`, the
source states the bound as `$`\prod_j |\text{pool}_j|`$` leaves and
`$`\sum_j \prod_{i \le j} |\text{pool}_i|`$` calls to `Match::get`, "reached only when
the guard refuses everything" (`space_matcher.rs:319-321`). Hence the total
matcher-side guard work for one receive is

```math
W \;=\; \Bigl(\prod_{j=0}^{l-1} |\text{pool}_j|\Bigr)\cdot E(G) \;+\; \Bigl(\sum_{j=0}^{l-1}\prod_{i\le j} |\text{pool}_i|\Bigr)\cdot M
```

where `$`E(G)`$` is one guard evaluation and `$`M`$` one spatial match. The charged
amount is `$`\Theta(G)`$` — independent of every factor in `$`W`$`.

This shape is a **consequence of the D1 repair**: before it, the search stopped
at the first spatial match per bind; enumerating instead is what makes a guarded
receive able to reach many leaves. The source is explicit that this is
consensus-visible and separates the two repairs so they can be reviewed apart
(`space_matcher.rs:283-294`). Any charge design has to price enumeration, and
the D1 discussion is where the pricing question was already half-asked.

The source also records a measured table on that crate's **test** matcher
(`space_matcher.rs:325-329`) — reproduced here as S-cited, **not** as this
document's measurement, and explicitly not the production guard cost:

| receive | store | `Match::get` | `check_commit` | release | debug |
|---|---|---|---|---|---|
| guarded, one bind, guard refuses all | 1000 on one channel | 1000 | 1000 | 1.01 ms | 17.0 ms |
| guarded, two binds, guard refuses all | 60 × 60 | 3660 | 3600 | 1.17 ms | 11.5 ms |
| UNGUARDED, two binds | 60 × 60 | 2 | 1 | 0.10 ms | 1.9 ms |

The test matcher's `check_commit` is trivial. The production question is what
those columns become when each of the 3600 calls is a substitution + encoding +
Presburger decision. That is [§7.3](#73-m1--the-guard-lane-zero) and
[§7.8](#78-m6--guard-lane-scaling-surface).

### 5.2 The three axes

| Axis | Question | Why it is the axis |
|---|---|---|
| **Pool size** `$`\lvert\text{pool}\rvert`$` | How does total guard work scale with the number of resting data on the bound channels? | Linear at `$`l=1`$`; the single-bind case "carries almost every guard in practice" (`space_matcher.rs:335-336`). Attacker controls it by sending. |
| **Join arity** `$`l`$` | How does it scale with the number of binds? | The exponent in `$`\prod_j`$`. Fixed by program text, not data (`space_matcher.rs:380-382`) — so it is author-controlled, not sender-controlled. |
| **Guard complexity** `$`G`$` | How does `$`E(G)`$` grow, and how does it differ between the two deciders? | The multiplicand. For the substrate leg, the count of *opaque fragments* is the interesting sub-axis: each one is a separate `rho_pure_eval` run (`guard_par_substrate.rs:840-846`), so a guard built from many opaque fragments multiplies evaluator runs within a single `check_commit`. |

### 5.3 Program-controlled versus bounded by construction

| Quantity | Controlled by | Bounded by |
|---|---|---|
| Pool size | Any sender to the channel | Nothing metered — a produce that never commits still enlarges the pool |
| Join arity `$`l`$` | The receiving program's author | Program text; constant per receive |
| Guard size `$`G`$` | The receiving program's author | Charged once, at `substitute_and_charge` |
| Guard evaluations `$`N`$` | **Senders**, via pool size | **Nothing** — this is the gap |
| Opaque fragments per guard | The author | Guard size |
| Fold body calls | Program | Charged COMM count (§4.2) |

The row that matters is `$`N`$`: it is the only quantity in the table that a third
party can inflate and that no charge tracks. Note the asymmetry that makes it a
DoS shape rather than a fairness problem — the *sender* pays a COMM charge to
enlarge the pool, but the *receiver's* guard is then re-evaluated across the
enlarged pool on every subsequent commit attempt, and nobody pays for those.

---

## 6. The constraint that complicates any guard metering design

**The solver budget is already consensus-critical for correctness, not merely for
cost.** This must be stated plainly to whoever designs guard metering, because it
removes the most obvious degree of freedom.

The substrate's decision procedures are budgeted by `SubstrateConfig::bit_width`,
fixed network-wide as `CONSENSUS_SUBSTRATE_CONFIG = SubstrateConfig::DEFAULT`
with `DEFAULT_BIT_WIDTH = 16`, i.e. integers over `$`[-32768,\,32767]`$`
(`prattail/src/guard_formula.rs:137`, `:196`, `:49`). The reason it is fixed is
recorded at the constant:

> If two nodes ran different budgets, one could reach `Sat` where the other
> reached `DontKnow` — a consensus fork.
> — `guard_formula.rs:167-175`

And the in-tree test `a_different_budget_reaches_a_different_verdict`
(`guard_formula.rs:2083-2092`) pins a concrete witness, **S-cited as measured by
that test**:

> `x < 100`. Under a 6-bit budget the integer domain is `$`[-32,32)`$`, so every
> representable `$`x`$` satisfies it and the guard is **Valid**; under the consensus
> budget (16-bit) it is merely **Contingent**.

The consequence for a metering design:

```text
   ┌─────────────────────────────────────────────────────────────────┐
   │  budget ↑  ⇒  more guards decided  ⇒  MORE work per decision     │
   │            ⇒  and DIFFERENT VERDICTS  ⇒  different COMMs fire    │
   │                                                                 │
   │  budget ↓  ⇒  cheaper decisions                                  │
   │            ⇒  and DIFFERENT VERDICTS  ⇒  different COMMs fire    │
   └─────────────────────────────────────────────────────────────────┘
```

So the budget **cannot be used as a cost-control knob.** Turning it down to make
guards cheaper is a protocol change that alters which communications happen; the
constant's own documentation says as much ("a guard that answered `DontKnow`
under the old budget may answer `Sat` under a larger one", `:185-187`). Cost
control for the guard lane has to come from somewhere other than the solver
budget — from charging, from bounding `$`N`$`, or from bounding `$`G`$` — and that is
the design constraint Greg's work inherits.

A second, subtler point in the same area: the run-time leg does not consult
`bit_width` at all, because a substituted guard is quantifier-free and
`evaluate_presburger_checked` reads the width only in its `Exists` arm
(`guard_par_substrate.rs:820-825`). So the budget bounds the *compile-time*
leg's domain, while the *run-time* leg's cost is bounded by guard size and
fragment count instead. The two legs need different cost models.

---

## 7. The measurement plan

Every experiment below is specified so it can be run without re-deriving any of
the groundwork. **No experiment here has been run.**

### 7.1 The instrument, and why it is not trustworthy by default

The instrument is `runtime.cost().total_cost()` — the canonical reconciled
consumed figure (`accounting/mod.rs:1227-1238`). Supporting readouts:

| Readout | Site | Use |
|---|---|---|
| `cost().total_cost()` | `accounting/mod.rs:1227` | The consensus-relevant aggregate |
| `cost().get()` / `remaining()` | `:935`, `:1240` | Initial minus consumed |
| `get_cost_event_log()` | `rho_runtime.rs:278` | Per-event `BillableTokenEvent` stream |
| `get_canonical_event_log()` | used by `rholang/tests/epathmap_charge_trace_spec.rs` | The rendered charge trace — the finest-grained view, and the model to copy |

**The instrument has exactly one way to lie, and it is a silent zero.** If the
budget is in unmetered mode, `total_cost()` returns a hard-coded `0`
(`accounting/mod.rs:1228-1230`) and `get()` returns `unsafe_max` (`:936-938`).
Every "the cost did not move" reading would then be vacuous. Correction C2
argues from source that mettail's runtime is *not* in that mode — but an
argument from source is exactly what a measurement is supposed to replace.
Hence T0.

`rholang/tests/epathmap_charge_trace_spec.rs` is the recommended template for
every experiment below: it already builds a fresh runtime, evaluates with a
fixed `Blake2b512Random` seed, renders the canonical event log to a stable
string form, and asserts determinism across two fresh runtimes.

### 7.2 T0 — the teeth test (mandatory gate)

> **No zero from any experiment below may be believed until T0 passes on the same
> runtime construction that experiment uses.**

**Hypothesis.** `runtime.cost().total_cost()` is live — strictly increasing in
charged work — on a runtime built by mettail's `build_runtime_with_definitions`
(`run.rs:500`) after `cost().set(Cost::unsafe_max())` (`run.rs:542`).

**Instrument.** `total_cost()` before and after `inj`, plus
`get_cost_event_log()`.

**Corpus.** Two programs differing only in a quantity known to be charged:

- `A`: `@"c"!(1) | for (@x <- @"c") { Nil }`
- `B`: `@"c"!(1) | @"d"!(2) | for (@x <- @"c") { Nil } | for (@y <- @"d") { Nil }`

**Procedure.** Build the runtime the way `run.rs` does; inject; read
`total_cost()`.

**Positive (instrument is live).** `total_cost(B) > total_cost(A) > 0`, and the
event log is non-empty for both. Proceed.

**Negative (instrument is dead).** `total_cost(A) == 0`, or the event log is
empty, or `A == B`. **Stop.** The budget is in unmetered mode, correction C2 is
wrong for this construction, and every downstream zero is meaningless. Diagnose
by reading `cost().get()`: an `i64::MAX` readout confirms unmetered mode.

**Secondary teeth test (T0b) — sensitivity to the right thing.** Vary *guard
size* with the candidate count held at 1:

- `A'`: `for (@x <- @"c" where x == 1) { Nil }` with one matching datum
- `B'`: same, with a guard of the same truth value but several times the term size

Expect `total_cost(B') > total_cost(A')`, because `substitute_and_charge`
(`reduce.rs:1571-1575`) is proportional to guard size. This proves the instrument
is sensitive **to the guard specifically**, closing the loophole where an
instrument detects COMMs but happens to be blind to everything guard-related.

### 7.3 M1 — the guard-lane zero

**Hypothesis.** The number of guard *evaluations* does not affect the charged
cost. Formally: with the receive, the guard term, and the number of sends held
fixed, `total_cost` is invariant under the number of candidate selections the
search must reject.

**Design — the confound and how it is removed.** Naively varying the pool size
also varies the number of sends, and sends are charged. The fix is to hold the
pool **identical** and vary only *which* datum satisfies the guard, exploiting
the canonical candidate order:

- `P_first`: `N` data resting on `@"c"`; guard satisfied by the datum that comes
  **first** in canonical order ⇒ 1 `check_commit`, which accepts.
- `P_last`: the **same** `N` data on `@"c"`; guard satisfied only by the datum
  that comes **last** ⇒ `N` `check_commit` calls, `N-1` of which reject.

Both programs have `N` sends, one receive, one guard of identical size, and both
end with exactly one datum consumed and `N-1` resting. Every charged quantity is
equal by construction; the only difference is guard evaluations.

**Corpus.** `N ∈ {1, 10, 100, 1000}`, single bind. Then the two-bind join with
pools `$`60 \times 60`$`, mirroring the S-cited table in §5.1 so the results are
comparable to it.

**Measure.** `total_cost(P_first)` versus `total_cost(P_last)` at each `N`; also
record wall time for both, to show the work is real even where the charge is not.

**Positive result — guard evaluation is unmetered.**
`total_cost(P_first) == total_cost(P_last)` for every `N`, while wall time for
`P_last` grows with `N`. Charge invariant, work linear: the gap is demonstrated,
not inferred.

**Negative result — some charge does track it.** Any dependence of `total_cost`
on which datum satisfies the guard. Then locate the charge in the event log and
this document's central claim is wrong; report it loudly.

**Run on both deciders.** mettail's runtime (`SubstrateGuardMatcher`, via
`run.rs:514`) and a runtime built with f1r3node's `Matcher`, to establish S1 and
S2 independently. The two rows are the same experiment with one line changed.

### 7.4 M2 — accrual under `unsafe_max`

**Hypothesis (correction C2).** `cost().set(Cost::unsafe_max())` leaves the
budget metered; charges accrue and `total_cost()` counts them; only the OOP
boundary is disabled.

**Procedure.** On one runtime, read `total_cost()` after `inj` for a program with
a known number of COMMs, under three budget settings: (i) `set(unsafe_max)` as
`run.rs:542` does; (ii) `set(Cost::create(K, …))` for a `K` large enough to
complete; (iii) a `K` too small to complete.

**Positive.** (i) and (ii) report the **same non-zero** `total_cost`; (iii)
fails with `OutOfPhlogistonsError`. That is exactly "metered but unbounded".

**Negative.** (i) reports `0` while (ii) reports non-zero ⇒ `unsafe_max` *does*
reach unmetered mode by some path not found in this reading, and C2 must be
withdrawn.

### 7.5 M3 — held-fold body cost versus COMM count

**Hypothesis.** The fold body's charge is independent of the body's actual work:
two fold sites differing only in operand magnitude charge identically, while the
arbitrary-precision arms' wall time diverges.

**Corpus.** A fold-bearing term evaluated at each `FoldKind`
(`fold_contract.rs:146-153`), with operands spanning small to very large for
`BigIntCast` / `BigRatCast` and the fixed-width arms as controls.

**Measure.** `total_cost()` and the event log (expecting only the driving COMMs),
plus wall time inside the handler.

**Positive.** Charge constant across operand magnitude; wall time constant for
the four fixed-width arms and growing for the two arbitrary-precision arms. This
localizes the exposure to exactly the two arms §4.2 predicts and quantifies how
much work one charged COMM can carry.

**Negative.** Charge tracks operand magnitude ⇒ something already charges the
body; find it in the event log.

### 7.6 M4 — on-chain reachability of the surface `where` guard

**Hypothesis.** A `where` guard written in Rholang source survives the full
deploy path — parse, normalize, sign, evaluate — and reaches
`Matcher::check_commit` on a validator.

**Procedure.** Take the shortest guarded program that parses; normalize it and
assert `Receive.condition.is_some()` on the resulting `Par` (the direct check on
`p_input_normalizer.rs:563`). Then run it through the cosigned deploy path
(`casper/src/rust/rholang/runtime.rs:566`,
`play_deploy_with_cost_accounting_cosigned`) and confirm the guard is consulted —
most cheaply by a guard whose verdict is observable in the resulting state
(a guard that rejects leaves the datum resting; one that accepts consumes it).

**Positive.** Guard reaches the validator ⇒ S2 is a **live** consensus-path DoS
surface and its severity stands as ★★★.

**Negative.** The surface syntax is not accepted from a signed deploy ⇒ S2 is
**latent**: present in the normalizer and the matcher, not reachable by a
deployer today. Severity drops, and the finding becomes "close it before the
syntax ships" rather than "close it now". **This is the single highest-value
experiment in the plan**, because it is the one that decides whether S2 is urgent
or merely important.

### 7.7 M5 — residual host-side evaluation sweep

**Hypothesis.** Beyond S1/S2/S4, no admitted exec path performs unmetered
host-side evaluation.

**Procedure — make it mechanical rather than a reading.** Enumerate every
`Definition` installed into a mettail-constructed runtime (the
`extra_system_processes` threaded at `run.rs:521` and `step.rs:636`) and, for
each, record what its handler computes. `ProcessContext` has no budget field, so
**every** such handler is unmetered by construction; the sweep is therefore a
*census of installed definitions*, not a search for a cost handle. Pair it with a
grep-based gate over `rholang-runtime` for host-side arithmetic reached from an
`inj` path.

**Positive.** The census is exactly {fold contracts, A-S3 native handlers}, both
COMM-gated as in §4.2.

**Negative.** Any installed definition whose handler does open-ended work not
gated behind a charged COMM. Report as a new site.

### 7.8 M6 — guard-lane scaling surface

**Purpose.** Supply Greg's design with the cost curve, since a charge cannot be
sized without one. **Measurement only; no charge is proposed.**

**Procedure.** Sweep the three axes of §5.2 and record wall time per
`check_commit`, on both deciders:

| Axis | Sweep | Held fixed |
|---|---|---|
| Pool size | `$`\lvert\text{pool}\rvert \in \{1,10,10^2,10^3,10^4\}`$` | `$`l=1`$`, guard fixed |
| Join arity | `$`l \in \{1,2,3\}`$` | per-pool size 60, guard fixed |
| Guard size | `$`G`$` over a ladder of guard terms | `$`l=1`$`, pool 1000 |
| Opaque-fragment count | 0, 1, 2, 4, 8 fragments | guard size held as constant as the ladder allows |

The last row is substrate-specific and has no analogue on f1r3node's decider: it
tests whether `substrate_guard_verdict`'s per-fragment `machine_verdict` loop
(`guard_par_substrate.rs:840-846`) makes a single `check_commit` cost several
evaluator runs.

**Deliverable.** A table of `$`E(G)`$` against each axis, and the implied `$`W`$` from
§5.1 — the input any charge sizing needs.

**Instrumentation note.** Counting `check_commit` calls needs a counter that does
not exist in production. Do **not** add one to a production decider. Wrap:
implement a test-only `Match` that delegates to the real decider and counts, and
install it via `RSpace::create` exactly as `run.rs:514` installs
`SubstrateGuardMatcher`. The `Match` trait object seam is what makes this
possible without touching production code — the same seam that made the whole
substrate wire possible in the first place.

### 7.9 Execution notes

- **Fixed seed.** `Blake2b512Random::create_from_bytes(…)`, never
  `create_from_length` (thread-`rng` nondeterminism); see the note in
  `epathmap_charge_trace_spec.rs`.
- **Determinism check.** Run each cell twice on fresh runtimes and require
  identical charge traces before believing either, as
  `deterministic_trace` in that spec does.
- **Crate-scoped runs.** The workspace gate is broken by unrelated in-flight
  work; use `cargo test -p <crate>` and say so when reporting.
- **Resource limits.** `systemd-run --user --scope -p MemoryMax=28G` for any
  heavy subprocess.
- **Tee everything** to a file so each cell is run once.

---

## 8. Evidence ledger

### 8.1 Provenance of every claim in this document

| Claim | Provenance |
|---|---|
| `ChargingRSpace` / `CostManager` do not exist (C1) | **Read** — tree-wide grep, zero definitions |
| `set(unsafe_max)` leaves the budget metered (C2) | **Read** — `accounting/mod.rs:944-947`, `:955-990`, and the complete enumeration of `unmetered` writes |
| mettail's runtime is built metered | **Read** — `cost_accounting.rs:16` vs `:18`; `rho_runtime.rs:1255` |
| No cost handle reaches `check_commit` | **Read, structural** — trait signature `rspace++/src/rspace/match.rs:30`; field-less `Matcher` `match.rs:14`; `SubstrateGuardMatcher` `guard_par_substrate.rs:692-695` |
| No cost handle reaches a system-process handler | **Read, structural** — `ProcessContext` `system_processes.rs:206-213`; `ContractCall` `contract_call.rs:30-33` |
| Guard is substituted-and-charged once per receive-eval | **Read** — `reduce.rs:1571-1575` |
| `check_commit` is consulted once per complete candidate selection | **Read** — `space_matcher.rs:396-405` |
| Surface `where` guard populates `Receive.condition` | **Read** — `p_input_normalizer.rs:489-507`, `:526`, `:563` |
| Surface `where` guard is reachable from a **signed deploy** | **UNVERIFIED** — M4 |
| The `$`1000 \times`$` / `$`60\times60`$` matcher table | **S-cited** — `space_matcher.rs:325-329`, that crate's **test** matcher; not this document's measurement and not production guard cost |
| `x < 100` Valid at 6-bit, Contingent at 16-bit | **S-cited** — `guard_formula.rs:2083-2092`, an in-tree test claiming to be a measured witness |
| `DEFAULT_BIT_WIDTH = 16`, fixed network-wide | **Read** — `guard_formula.rs:49`, `:137`, `:196` |
| Speculation sandbox starts at zero and funds from the host | **Read** — `speculation.rs:749`, `:762-770`, `:802-809` |
| Fold arms `BigIntCast`/`BigRatCast` are magnitude-dependent | **Read** — `fold_contract.rs:144-155`; magnitude scaling itself is **UNVERIFIED**, M3 |
| No residual host-side exec-path evaluation beyond S4 | **Read, non-exhaustive** — see §4.5; M5 makes it exhaustive |

### 8.2 What was measured

**Nothing.** No build, benchmark, or test was run in the course of producing this
document. Every experiment in §7 remains unexecuted. The audit's conclusions are
structural (type signatures and field lists, which are compile-time facts) or
textual (source comments, cited as such).

---

## 9. Seam inventory — where a charge could be levied

**This section identifies seams. It proposes no charge.** For the guard lane it
is explicitly input to a design owned elsewhere.

| Site | Handle reachable today? | Nearest existing seam | What would have to change |
|---|---|---|---|
| S1 / S2 `check_commit` | **No** | The `Match` trait object installed at `RSpace::create` | The `Match` trait lives in `rspace++`, *below* `rholang`; a budget cannot be referenced from there without either a layering change or passing a charge sink into `RSpace::create`. **Both are consensus-affecting and both belong to Greg's design.** |
| S1 / S2, alternative | — | `reduce.rs:1563`, where `reserve_comm` already fires and the handle **is** in scope | A charge levied at receive-eval can only price the guard *a priori* (its size), not its realized evaluation count. Recording this because it is the seam that exists without any layering change — its limitation is the point. |
| S4 fold handler | **No** | `Definition::handler`'s `ProcessContext` | Adding a budget to `ProcessContext` would give every system process a handle. Wide blast radius; the COMM gate of §4.2 may make it unnecessary. |
| S3 drivers | **Yes** | `runtime.cost()` in scope at `run.rs:542`, `step.rs:642` | Nothing structural; the question is policy, not reachability. |
| S6 sandbox | **Yes** | `fund_from` / `reserve_comm(sandbox.consumed())` | Already correct. |

The established two-part idiom for a size-dependent charge, where a handle
exists, is `reserve_primitive` (`metering.rs:133`) for the fixed part and
`reserve_incremental_primitive` (`:138`, which no-ops on zero and rejects
negatives) for the size-dependent part.

**The standing rule that governs all of the above:** no charge table, counter, or
budget may be added in mettail. If a fix requires one, the work belongs on the
f1r3node side of the seam — and for the guard lane, in Greg's design.

---

## 10. References

**f1r3node** (`/home/dylon/Workspace/f1r3fly.io/f1r3node-rust-mettail`)

- `rholang/src/rust/interpreter/accounting/mod.rs` — `RuntimeBudget`; `get` `:935`, `set` `:944`, `reset_from_token` `:955`, `set_unmetered` `:1196`, `enter_unmetered_scope` `:1207`, `total_cost` `:1227`
- `rholang/src/rust/interpreter/accounting/costs.rs` — `Cost::unsafe_max` `:72`, `send_eval_cost` `:326`, `receive_eval_cost` `:328`
- `rholang/src/rust/interpreter/accounting/cost_accounting.rs` — `empty_cost` `:16`, `unmetered_cost` `:18`
- `rholang/src/rust/interpreter/accounting/has_cost.rs:5-7` — the `HasCost` trait
- `rholang/src/rust/interpreter/metering.rs` — `MeteredMachine`; `reserve_comm` `:96`, `reserve_reduction` `:129`, `reserve_primitive` `:133`, `reserve_incremental_primitive` `:138`, `reserve_substitution` `:153`
- `rholang/src/rust/interpreter/reduce.rs` — `eval_receive` `:1553`, COMM charge `:1563`, guard substitution `:1571-1575`, per-bind pattern substitution `:1587`
- `rholang/src/rust/interpreter/matcher/match.rs` — `Matcher` `:14`, `check_commit` `:79`, `SpatialMatcherOracle` `:120`, `guard_passes` `:141`
- `rholang/src/rust/interpreter/rho_runtime.rs` — `MeteredMachine` construction `:1084`, budget construction `:1255`
- `rholang/src/rust/interpreter/system_processes.rs` — `ProcessContext` `:206`, `Definition` `:247`
- `rholang/src/rust/interpreter/contract_call.rs:30` — `ContractCall`
- `rholang/src/rust/interpreter/compiler/normalizer/processes/p_input_normalizer.rs` — guard normalization `:489-507`, `:526`, `:563`
- `rspace++/src/rspace/match.rs:30` — the `Match::check_commit` default
- `rspace++/src/rspace/space_matcher.rs` — cost documentation `:311-339`, `extract_guarded_data_candidates` `:340`, `search_candidate_selection` `:387`, the leaf `:396-405`
- `rholang/tests/epathmap_charge_trace_spec.rs` — the charge-trace harness template
- `casper/src/rust/rholang/runtime.rs:570` — `play_deploy_with_cost_accounting_cosigned`

**mettail** (`/home/dylon/Workspace/f1r3fly.io/mettail-rust`)

- `rholang-runtime/src/run.rs` — `build_runtime_with_definitions` `:500`, matcher install `:514`, `create_rho_runtime` `:517`, `inj_on_runtime` `:538-546` (budget `:542`)
- `rholang-runtime/src/step.rs` — matcher install `:627`, runtime `:632`, budget `:642`
- `rholang-runtime/src/guard_par_substrate.rs` — `SubstrateGuardMatcher` `:692`, `check_commit` `:721`, `substrate_guard_passes` `:749`, `substrate_guard_verdict` `:826`, `substitute_bound_pars` `:892`
- `rholang-runtime/src/guard_discharge.rs` — module header `:1-111`, consensus consequence `:105-111`, `GuardDischarge` `:126`
- `rholang-runtime/src/fold_contract.rs` — `fold_eval` `:144`, `fold_definition` `:202`
- `rholang-runtime/src/speculation.rs` — matcher `:749`, the deliberate absence of `unsafe_max` `:762-770`, `fund_from` `:802`
- `prattail/src/guard_formula.rs` — bit-width note `:49`, `SubstrateConfig::DEFAULT` `:137`, `CONSENSUS_SUBSTRATE_CONFIG` `:196`, `dont_know_policy` `:868`, budget tests `:2072-2092`

**Related suites**

- [Semantic Predicates — 18, The `where`-Guard Substrate Wire](../../architecture/semantic-predicates/18-the-where-guard-substrate-wire.md)
- [Semantic Predicates — 08, Runtime COMM Enforcement](../../architecture/semantic-predicates/08-runtime-comm-enforcement.md)
- [Rho-Native Integration — 13, Knotted-Topoi Operational Invariants](../../architecture/rho-native-integration/13-knotted-topoi-operational-invariants.md) (INV-14, INV-14b′)
