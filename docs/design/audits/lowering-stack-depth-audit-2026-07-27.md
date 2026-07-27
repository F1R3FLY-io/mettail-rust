# The RhoCalc Lowering's Native-Stack Profile — Audit, Measurement, and Conversion Standard (2026-07-27)

**Status.** Measurement-derived audit. Every quantitative claim below was **measured on this
tree, on this machine, on 2026-07-27**, with the harnesses named alongside each table
(`rholang-runtime/tests/stack_depth_gate.rs`, and the bisection scripts reproduced in
Appendix A). Numbers reproduced from an earlier report rather than re-measured are labelled
*reported*.

**Scope.** `rholang-runtime/src/rhocalc_ast.rs` — the translation from MeTTaIL's `rhocalc`
AST (`Proc`, `Name`, …) to a normalized `rhoapi::Par`. This is the **lowering**. It is not the
parser (measured here, and clean — §6) and it is not the f1r3node reducer (a separate,
independently-measured family — §2).

---

## 1. The defect

A traversal whose native-stack consumption is proportional to the **nesting depth of the term
it walks** turns a small input into a process abort. A stack overflow is a `SIGSEGV` delivered
on the guard page: it is neither a panic nor unwindable, so it takes down the whole process
rather than failing one deploy.

The reported reproducer is 30 bytes of RhoCalc:

```
@"OUT"!([[[[[[ … [1] … ]]]]]])
```

Located under `gdb`:

```text
Thread 1 "rhocalc" received signal SIGSEGV, Segmentation fault.
mettail_rholang_runtime::rhocalc_ast::lower_proc () at rholang-runtime/src/rhocalc_ast.rs:931
Backtrace stopped: Cannot access memory        ← the guard page
```

### 1.1 ★ Why `RUST_MIN_STACK` is inert on this path

`rholang-runtime/src/bin/rhocalc.rs` is `#[tokio::main] async fn main`, so **parsing and
lowering run on the process's main thread**. `RUST_MIN_STACK` is consulted only by
`std::thread`'s spawn path; it cannot resize a main thread, whose size is fixed by
`ulimit -s` before `main` is entered.

A sweep of `RUST_MIN_STACK` from 1 MiB to 32 MiB against a demo therefore reported "ok" at
every value **because it was controlling nothing**. Any remedy phrased in terms of that
variable — including the run-sheet prefixes retired by this work (§7) — was inert for the
main-thread half of the pipeline.

---

## 2. ★ There are TWO independent overflow sites, and they are easy to confuse

Measured on `target/debug/rhocalc` with the shared probe of Appendix A:

| depth | `ulimit -s` | `RUST_MIN_STACK` | faulting thread |
|---|---|---|---|
| 133 | 8,192 KiB | unset | **`tokio-rt-worker`** |
| 133 | 8,192 KiB | 1 GiB | *(survives)* |
| 170 | 8,192 KiB | unset | **`main`** |
| 170 | 8,192 KiB | 1 GiB | **`main`** |

```
  ┌──────────────────────── one `rhocalc` process ────────────────────────┐
  │                                                                       │
  │   main thread                          tokio-rt-worker                │
  │   ┌───────────────────────┐            ┌────────────────────────────┐ │
  │   │ Proc::parse_via_wpda  │            │ f1r3node reducer /         │ │
  │   │        ▼              │            │ normalizer / sorter        │ │
  │   │ rhocalc_ast::         │  lowered   │                            │ │
  │   │   lower_proc  ────────┼───Par─────▶│  substitute · sort_match · │ │
  │   │                       │            │  pretty · clone            │ │
  │   └───────────────────────┘            └────────────────────────────┘ │
  │    governed by `ulimit -s`              governed by `RUST_MIN_STACK`   │
  │    ★ THIS AUDIT'S SUBJECT               ✗ a different family          │
  └───────────────────────────────────────────────────────────────────────┘
```

Program order explains the interleaving completely — lowering runs *before* reduction, so
whichever limit binds first at a given depth is the one that reports:

| depth range | outcome |
|---|---|
| `d ≤ 132` | both survive |
| `133 ≤ d ≤ 169` | main survives; the **tokio worker** overflows |
| `d ≥ 170` | **main** overflows; the worker is never reached |

★ **Consequence worth stating plainly.** The user-visible "it stops working somewhere around
130" boundary is *not* `lower_proc`. It is the reducer, on the worker. `lower_proc`'s own
boundary was 169. Converting the lowering raises the main-thread ceiling; the **user-visible**
ceiling does not move past 132 until the reducer family is converted as well.

### 2.1 Threshold reconciliation

Two thresholds were in circulation before this audit. Both were correct about different
things; the discrepancy was not a measurement error.

| source | claim | resolution |
|---|---|---|
| bug report | "depth 128 runs, 144 faults" at the default stack | an **upper bound**: the `nest-*.rho` ladder steps 128 → 144, so the true value lies in `(128, 144]`. Bisected: `D_max` = **132**, first failure **133** — and that failure is on the **tokio worker**. |
| least-squares fit | `D_max ≈ 167` | a fit of the **main-thread-isolated** bisection, so it predicts the main-thread threshold. Bisected: `D_max` = **169**. Agreement 1.2%. |

The probe program was verified byte-identical between the two experiments with `cmp`, so the
probe is excluded as a source of the difference.

---

## 3. Baseline: the recursive form

`bisect_ulimit.sh`, 4 KiB resolution, `RUST_MIN_STACK` pinned to 1 GiB so only the main thread
binds. Debug profile (this workspace sets `codegen-backend = "cranelift"` for `[profile.dev]`).

| depth `N` | min `ulimit -s` (KiB) |
|---|---|
| 25 | 1,376 |
| 50 | 2,560 |
| 100 | 4,928 |
| 200 | 9,648 |
| 400 | 19,100 |

Pairwise slopes, in KiB per level: 47.36, 47.36, 47.20, 47.26. Linear; no curvature.

Let `S(N)` be the minimum viable stack, in KiB, at nesting depth `N`. Least squares gives

```math
S(N) \;=\; 197.5 \;+\; 47.257\,N \qquad\text{(KiB)},
```

that is **48,392 bytes per nesting level**, with a fixed intercept of about 198 KiB.

Two independent prior measurements agree: 48,640 B/level (0.5%) and 48,417 B/level (0.05%).

---

## 4. Attribution: why the constant was so large

`lower_proc` was a single function containing a **89-arm `match`** over `Proc`
(`rhocalc_ast.rs:939-1491`), with self-recursive calls in many arms.

At `-O0`, `rustc` does not overlay the stack slots of mutually exclusive match arms. A
function carrying `A` arms therefore reserves, in one frame, the sum of every arm's locals:

```math
\mathrm{frame}(\texttt{lower\_proc}) \;\approx\; \sum_{a=1}^{A}\mathrm{locals}(a),
```

and because the function is self-recursive, that sum is paid **once per nesting level**. With
`Par` being a `prost` message of eight `Vec` fields plus a bitset (~224 bytes), and most arms
needing two or three `Par`/`Result<Par, _>` temporaries, `89 × 3 × 224 ≈ 60` KB is the right
order of magnitude for the measured 48 KB — so the hypothesis was quantitatively plausible
before it was tested.

### 4.1 ★ The recursion SCC has 19 members, not one

This is the audit's most consequential structural finding, and it invalidates any conversion
scoped to "the self-recursive call sites of `lower_proc`".

The reported reproducer does not recurse through a self-call at all:

```
lower_proc ▸ CastList arm ▸ lower_list ▸ lower_proc ▸ CastList arm ▸ lower_list ▸ …
```

It recurses through a **helper**. Converting only `lower_proc`'s direct self-calls would leave
the reported reproducer exactly as it is.

A Tarjan strongly-connected-component decomposition of the call graph of `rhocalc_ast.rs` and
`rhocalc_formula.rs` puts **19 functions** in one component with `lower_proc`:

| member | line | reachable by |
|---|---|---|
| `lower_proc` | 931 | — |
| `lower_proc_in_env` | 927 | public alias |
| `lower_list` | 2447 | `[a, b, …]` |
| `lower_set` | 2501 | `Set(…)` |
| `lower_bag` | 2394 | `#{…}#` |
| `lower_map` | 2469 | `{k : v}` |
| `lower_pathmap` | 2527 | `{\| k : v \|}` |
| `lower_name` | 3223 | `@P`, channels |
| `lower_drop` | 3205 | `*n` |
| `lower_method` | 1687 | `x.size()` |
| `lower_binary_expr` | 1639 | `a - b`, `a < b` |
| `lower_concat` | 1784 | `l.concat(r)` |
| `lower_length` | 1751 | `l.length()` |
| `lower_nth` | 1766 | `l.nth(i)` |
| `lower_pfor_user` | 2575 | `for(…){…}` |
| `lower_body_lifting_folds` | 2261 | `new` / receive bodies |
| `lower_lookahead_operand` | 2950 | `x!(P)[*]` |
| `lower_pattern_proc` | 2807 | receive patterns |
| `lower_formula_in_env` | `rhocalc_formula.rs:102` | `t matches φ` |

Every edge in this component is traversable an unbounded number of times by a program, so
**the whole component must be driven by one machine**. A conversion covering a proper subset
leaves a reachable Θ(depth) path.

---

## 5. M-1 — the per-arm frame split (landed)

**Hypothesis `H1`.** The measured 48,392 B/level is dominated by `lower_proc`'s own frame, for
the reason in §4.

**Intervention.** Every one of the 89 arm bodies hoisted into its own `#[inline(never)]` free
function, parameters typed from the generated `Proc` enum. Pure code motion — no expression
rewritten; each call site retains the documentation explaining its semantics. `#[inline(never)]`
is load-bearing: without it the backend may re-inline the callees and restore the sum.

**Result.** Same instrument, same probe, same machine:

| depth `N` | baseline (KiB) | M-1 (KiB) |
|---|---|---|
| 25 | 1,376 | 548 |
| 50 | 2,560 | 896 |
| 100 | 4,928 | 1,640 |
| 200 | 9,648 | 3,116 |
| 400 | 19,100 | 6,080 |

```math
S_{\text{baseline}}(N) = 197.5 + 47.257\,N,
\qquad
S_{\text{M-1}}(N) = 165.5 + 14.777\,N \qquad \text{(KiB)}.
```

| | baseline | M-1 | factor |
|---|---|---|---|
| bytes per level (debug) | 48,392 | **15,132** | **3.20×** (68.7% removed) |
| `D_max`, main thread at 8 MiB | 169 | **542** | 3.21× |

**Verdict — `H1` partially confirmed.** The 89-arm match was the single largest contributor,
but not the whole cost: **15,132 B/level survives**, distributed over the other 18 SCC members
of §4.1 and the iterator-adapter frames of the `.collect::<Result<Vec<_>, _>>()` sites.

★ **This is a constant-factor result and must not be read as a fix.** The traversal remains
Θ(depth); `D_max` merely moved from 169 to 542. It is reported as a measured *attribution* —
how much of the constant the arm-splitting owned — which is precisely the question it was run
to answer.

---

## 6. ★ M-6 — the parser, measured

The parse path had never been measured on this axis. "Not measured" must not be allowed to
read as "not present", so it was measured, on both axes, with explicit thread stack sizes.

| subject | parameter 16 | 32 | 64 | 128 | slope |
|---|---|---|---|---|---|
| `parse_depth` | 471,040 B | 471,040 | 471,040 | 471,040 | **0** |
| `parse_width` | 471,040 B | 471,040 | 471,040 | 471,040 | **0** |

Identical to the byte at every rung: a large **fixed** intercept (~460 KiB of generated
recognizer tables and driver frame) and a slope of exactly zero, on both axes.

The parser is therefore **not** a member of this family. The reason is structural rather than
fortunate: `prattail/src/sppf_realize.rs:164` already drives SPPF realization from an explicit
worklist,

```rust
let mut stack: Vec<(SppfId, Phase)> = vec![(root, Phase::Enter)];
```

rather than from the host stack.

★ This doubles as the **existence proof for the conversion standard in §8**: the discipline the
lowering needs is not a novel construction to be argued about — it is the idiom already running
one stage earlier in the same pipeline, and the table above is the measurement showing that
idiom delivers a flat profile in production.

---

## 7. M-7 — the run-sheet prefixes (retired)

`demos/flt-church-desk/RUN-SHEET.md` prefixed every run line with
`RUST_MIN_STACK=134217728`, and a gate asserted the prefix was **present**.

Measured: all six committed `flt-church-desk` demos and all seven `flt-assay-desk` demos run to
their documented exit status with **no** `RUST_MIN_STACK` set, at the default `ulimit -s`
(`divergence.rho` exits 70 — its documented fuel-exhaustion beat — with no stack overflow).

The prefixes are removed and the gate is **inverted**: `no_run_line_in_the_sheet_carries_a_
stack_prefix` now asserts absence, backed by `every_committed_demo_runs_at_the_default_stack`,
which runs each committed demo with `env_remove("RUST_MIN_STACK")` and asserts no overflow.

The gate is kept pointing the other way rather than deleted, for two reasons:

1. **It is the regression detector for the fix.** If a depth-proportional traversal returns to
   this path, the natural repair under presentation pressure is to put the prefix back. That
   must fail the build and name the real gate instead.
2. **The prefix was never a correct remedy here.** Per §1.1 it could not reach the main thread
   at all. A sheet that recommends an inert knob teaches a presenter to mis-diagnose.

---

## 8. The conversion standard (M-2, outstanding)

The class is removed by driving the whole SCC of §4.1 from one explicit worklist, in the idiom
of `sppf_realize.rs:164`.

**Machine.** A deterministic, finite-control, **data-stack** transducer over a ranked tree.
The stack alphabet is data-bearing (borrowed pointers and child counts) and therefore
unbounded, so this is a *stack machine*, not a formal pushdown automaton — the document says so
rather than claiming a class it does not occupy.

* control: `{Enter, Combine} × Σ`, finite;
* `δ` has exactly two shapes —
  * **Enter**: push `Combine(k)`, then push children in **reverse**, so LIFO pops them
    left-to-right;
  * **Combine**: pop `arity(k)` values, apply the arm's post-order body, push one value;
* final configuration: work empty, exactly one value.

**Deficit invariant**, asserted at the head of the drive loop behind `debug_assert!`:

```math
|\mathit{vals}| \;+\; \bigl|\{\,\texttt{Enter} \in \mathit{work}\,\}\bigr|
\;=\; 1 \;+\; \sum_{\texttt{Combine}(k)\,\in\,\mathit{work}} \mathrm{arity}(k).
```

`arity` is written as an exhaustive `match`, deliberately duplicating the pop counts, because
the point is to cross-check them against an independent statement. This fires on the first
malformed configuration on **any** term, whereas a differential fires only if the corpus
happens to contain the witness.

### 8.1 Constraints that are not negotiable

* **`BoundEnv` is carried as a delta, never owned per work item.** `BoundEnv` holds a
  `HashMap<FreeVar<String>, usize>`, FLT hole levels and a resolver. An owned environment per
  work item clones that map per level, which leaves the traversal Θ(depth) anyway — refuted
  experimentally on the sibling f1r3node conversion. Work items carry an index into an
  environment arena; a new environment is materialised once per **binder site**, exactly as the
  recursive form does.
* **No weight domain.** An earlier design proposed `impl HeapSemiring for LowerWeight`. It was
  withdrawn on analysis: the one genuine `⊕` (`lower_proc_alternatives`' `Par::append` fold)
  fires **once, at the root**, over already-lowered whole alternatives — not at every meet point
  of a reachability computation — and `⊗` fails outright, because `Par` construction is n-ary
  and labelled, hence non-associative with no identity. `zero`/`is_zero`/`approx_eq` would be
  vacuous, and the impl would imply `poststar`/`prestar` apply to the lowering, which they do
  not. The depth fix comes from the pushdown part, not from a weight.
* **★ No early disambiguation.** Folding the recursion out of `collect_proc_alternatives` must
  not move the `⊕` from the root into per-node merges. Merging at every node *is* the weighted
  reading, and it would collapse readings early — the loss the project's standing
  "never disambiguate early" mandate forbids, reached by the back door of "integrating the merge
  into the driver". The fold removes *recursion*; it must not move the *merge point*.

### 8.2 Acceptance gates

| # | gate | discharge |
|---|---|---|
| 1 | `⊕` fires once, at the root, over whole lowered alternatives | code + test |
| 2 | pre-dedup set, post-dedup set and dedup keys identical to a retained recursive oracle twin | differential test |
| 3 | the `Par::append` fold is invariant under permutation of the alternative list | property test |
| 4 | the driver is a genuine instance of `sppf_realize.rs:164`'s idiom; any divergence named with a one-sentence reason | doc comment + review |
| 5 | `lower_depth`, `lower_add`, `lower_par` move from the tripwire into the converted list, **in both profiles** | `stack_depth_gate.rs` |

⚠ The `.collect::<Result<Vec<_>, _>>()` → `for` + `with_capacity` + `push` change is worth
roughly 12 of the 15 frames per level, and must be **absorbed into M-2** rather than committed
alone: a ~4× constant win moves `D_max` from ~542 to ~2,000 and would read as success while
leaving the class intact.

### 8.3 ⚠ Not a member of this family

`prattail/src/lint/lints.rs:5193`'s `max_depth` (PAR01) walks the **category reference
digraph** with cycle cutting. Its value is bounded by the number of categories and fixed at
grammar-compile time: it measures a static constant, not growth in input nesting. It is useful
codegen hygiene and nothing more.

---

## Appendix A — reproducing the measurements

The probe program, at nesting depth `d`:

```bash
{ printf '@"OUT"!('; for ((i=0;i<d;i++)); do printf '['; done; printf '1';
  for ((i=0;i<d;i++)); do printf ']'; done; printf ')\n'; } > nest-$d.rho
```

Minimum viable `ulimit -s` at a fixed depth (exponential probe, then bisect to 4 KiB):

```bash
runs() { ( ulimit -c 0; ulimit -s "$1"; exec target/debug/rhocalc "$2" >/dev/null 2>&1 ); }
```

⚠ Two hygiene rules, both learned the hard way:

* **`ulimit -c 0` on every probe.** A core dump of this binary is ~305 MB, and a bisection
  produces dozens of faults.
* **`RUST_MIN_STACK` pinned high** (1 GiB) when measuring the lowering. Leaving it unset makes
  the tokio worker bind first beyond depth ≈ 133 and reports "no `ulimit` works" — which is
  true, and about the wrong traversal (§2).

In-process, profile-independent measurement is `rholang-runtime/tests/stack_depth_gate.rs`,
which runs each subject on a thread created with an explicit `stack_size` — the one mechanism
that binds regardless of how the code is reached in production — and bisects. Its
`report_slopes` test is the measurement instrument:

```bash
cargo test -p rholang-runtime --features "rhocalc-runtime lambda-runtime calculator-runtime" \
  --test stack_depth_gate -- --ignored --exact report_slopes --nocapture
```

---

## Appendix B — status

| step | state | measured |
|---|---|---|
| instruments + baseline | ✅ | 48,392 B/level; `D_max` 169 (main) / 132 (default) |
| threshold reconciliation | ✅ | §2.1 |
| SCC enumeration | ✅ | §4.1 — 19 members |
| M-1 per-arm split | ✅ landed | 15,132 B/level (3.20×) |
| M-2 explicit-stack driver | ☐ outstanding | — |
| M-3/M-4 `collect_proc_alternatives`, ambiguity-nesting axis | ☐ outstanding | — |
| M-5 gate | ✅ landed | tripwire + width axis green |
| M-6 parser probe | ✅ | 0 B/level, 0 B/sibling |
| M-7 run-sheet prefixes | ✅ landed | 13 demos green at the default stack |
