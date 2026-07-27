# The Rholang Lowering's Native-Stack Profile — Audit, Measurement, and Conversion Standard (2026-07-27)

**Status.** Measurement-derived audit. Every quantitative claim below was **measured on this
tree, on this machine, on 2026-07-27**, with the harnesses named alongside each table
(`rholang-runtime/tests/stack_depth_gate.rs`, and the bisection scripts reproduced in
Appendix A). Numbers reproduced from an earlier report rather than re-measured are labelled
*reported*.

**Scope.** `rholang-runtime/src/rholang_ast.rs` — the translation from MeTTaIL's `rholang`
AST (`Proc`, `Name`, …) to a normalized `rhoapi::Par`. This is the **lowering**. It is not the
parser (measured here, and clean — §6) and it is not the f1r3node reducer (a separate,
independently-measured family — §2).

---

## 1. The defect

A traversal whose native-stack consumption is proportional to the **nesting depth of the term
it walks** turns a small input into a process abort. A stack overflow is a `SIGSEGV` delivered
on the guard page: it is neither a panic nor unwindable, so it takes down the whole process
rather than failing one deploy.

The reported reproducer is 30 bytes of Rholang:

```
@"OUT"!([[[[[[ … [1] … ]]]]]])
```

Located under `gdb`:

```text
Thread 1 "rholang" received signal SIGSEGV, Segmentation fault.
mettail_rholang_runtime::rholang_ast::lower_proc () at rholang-runtime/src/rholang_ast.rs:931
Backtrace stopped: Cannot access memory        ← the guard page
```

### 1.1 ★ Why `RUST_MIN_STACK` is inert on this path

`rholang-runtime/src/bin/rholang.rs` is `#[tokio::main] async fn main`, so **parsing and
lowering run on the process's main thread**. `RUST_MIN_STACK` is consulted only by
`std::thread`'s spawn path; it cannot resize a main thread, whose size is fixed by
`ulimit -s` before `main` is entered.

A sweep of `RUST_MIN_STACK` from 1 MiB to 32 MiB against a demo therefore reported "ok" at
every value **because it was controlling nothing**. Any remedy phrased in terms of that
variable — including the run-sheet prefixes retired by this work (§7) — was inert for the
main-thread half of the pipeline.

---

## 2. ★ There are TWO independent overflow sites, and they are easy to confuse

Measured on `target/debug/rholang` with the shared probe of Appendix A:

| depth | `ulimit -s` | `RUST_MIN_STACK` | faulting thread |
|---|---|---|---|
| 133 | 8,192 KiB | unset | **`tokio-rt-worker`** |
| 133 | 8,192 KiB | 1 GiB | *(survives)* |
| 170 | 8,192 KiB | unset | **`main`** |
| 170 | 8,192 KiB | 1 GiB | **`main`** |

```
  ┌──────────────────────── one `rholang` process ────────────────────────┐
  │                                                                       │
  │   main thread                          tokio-rt-worker                │
  │   ┌───────────────────────┐            ┌────────────────────────────┐ │
  │   │ Proc::parse_via_wpda  │            │ f1r3node reducer /         │ │
  │   │        ▼              │            │ normalizer / sorter        │ │
  │   │ rholang_ast::         │  lowered   │                            │ │
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
(`rholang_ast.rs:939-1491`), with self-recursive calls in many arms.

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

### 4.1 ★ The recursion SCC has 19 members, not one — and 87 after M-1

This is the audit's most consequential structural finding, and it invalidates any conversion
scoped to "the self-recursive call sites of `lower_proc`".

The reported reproducer does not recurse through a self-call at all:

```
lower_proc ▸ CastList arm ▸ lower_list ▸ lower_proc ▸ CastList arm ▸ lower_list ▸ …
```

It recurses through a **helper**. Converting only `lower_proc`'s direct self-calls would leave
the reported reproducer exactly as it is.

A Tarjan strongly-connected-component decomposition of the call graph of `rholang_ast.rs` and
`rholang_formula.rs` puts **19 functions** in one component with `lower_proc`:

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
| `lower_formula_in_env` | `rholang_formula.rs:102` | `t matches φ` |

Every edge in this component is traversable an unbounded number of times by a program, so
**the whole component must be driven by one machine**. A conversion covering a proper subset
leaves a reachable Θ(depth) path.

#### 4.1.1 ★ RE-DERIVED after M-1: the component has **87** members, not 19

The table above was derived **before** M-1. M-1 hoisted each of `lower_proc`'s 89 arm bodies
into its own `#[inline(never)]` free function (§5); 68 of those 68 arms call back into the
component, so each became a member of it. Re-derived on the M-1 tree:

```math
|\mathrm{SCC}| \;=\; \underbrace{19}_{\text{helpers}} \;+\; \underbrace{68}_{\text{recursive } \texttt{lower\_arm\_*}} \;=\; 87 ,
```

with the remaining `89 - 68 = 21` arms being leaves (`lower_arm_p_zero`, the ground-literal
casts, the fail-closed arms, `lower_arm_p_var`, `lower_arm_unsupported`, …) which call nothing
in the component and are therefore **not** members.

★ This matters for scoping, not for bookkeeping. "Convert the SCC" read against the 19-member
table understates the work by 78%, and — worse — the 68 arms are precisely where the per-level
frames live after M-1.

#### 4.1.2 The re-derivation method, so the number is reproducible

The component is recovered from source by the following procedure, which needs no build and no
type information. It is stated in full rather than cited, because the *only* thing that makes
"87" checkable is being able to run it again.

```
INPUT   the translation units that form the lowering:
        rholang-runtime/src/rholang_ast.rs, rholang-runtime/src/rholang_formula.rs

1  ERASE NOISE.  Replace every line comment, block comment, string literal, raw string
   literal and char literal by an equal number of spaces (newlines preserved, so byte
   offsets and line numbers survive).  Rationale: an identifier inside a doc comment or a
   diagnostic message must not be mistaken for a call site — `rholang_ast.rs` documents
   `lower_list` dozens of times in prose.

2  LOCATE DEFINITIONS.  For each match of /^(pub )?(pub\(crate\) )?fn NAME/ in the erased
   text, delimit the body by matching the parameter list's parentheses, skipping the return
   type and any where-clause, then brace-matching from the first `{`.  A definition whose
   signature is followed by `;` (a trait declaration) has no body and is skipped.
   Definitions nested inside another definition's span are folded into their parent.

3  EDGES.  Inside each body, every word-boundary-delimited occurrence of a NAME found in
   step 2, followed by `(`, `::<` or `)` — the last covers a function passed by value —
   is an edge caller → callee.

4  TARJAN.  Run Tarjan's strongly-connected-components algorithm on the digraph.  Report
   every component of size > 1, plus every singleton with a self-loop (a directly
   self-recursive function, e.g. `lower_int_value`).
```

Step 4's second clause is not a detail: it is what surfaced `lower_int_value`, a
**self-recursive function that is not in the component** (it calls nothing that reaches
`lower_proc`) and therefore had its own Θ(depth) axis through nested `Int::NegInt`. A
conversion scoped to the component would have left `- - - … - 5` exactly as it was. It is
converted, and gated by the `lower_neg` subject.

Running the procedure on the M-1 tree also reports three unrelated components, recorded so
that "not converted" is never mistaken for "not examined": `{replace_fold, replace_fold_in_name,
rebuild_binary}` and `{find_fold, find_fold_in_name}` (both walk a body once per **fold site**,
not once per nesting level, and both are called BY the driver rather than from inside it), and
`{proc_has_machine_effects, name_has_machine_effects}` (a predicate on the raw term, outside the
lowering).

---

## 5. M-1 — the per-arm frame split (landed)

**Hypothesis `H1`.** The measured 48,392 B/level is dominated by `lower_proc`'s own frame, for
the reason in §4.

**Intervention.** Every one of the 89 arm bodies hoisted into its own `#[inline(never)]` free
function, parameters typed from the generated `Proc` enum. Pure code motion — no expression
rewritten; each call site retains the documentation explaining its semantics. `#[inline(never)]`
is load-bearing: without it the backend may re-inline the callees and restore the sum.

**Result.** Same instrument, same probe, same machine. ★ **Both profiles**, because the
acceptance criteria require it — and because, as it turns out, the profiles disagree
qualitatively rather than merely by a factor.

Debug (cranelift, `-O0`):

| depth `N` | baseline (KiB) | M-1 (KiB) |
|---|---|---|
| 25 | 1,376 | 548 |
| 50 | 2,560 | 896 |
| 100 | 4,928 | 1,640 |
| 200 | 9,648 | 3,116 |
| 400 | 19,100 | 6,080 |

Release (LLVM, `opt-level = 3`) — a deeper ladder, since the per-level cost is far smaller:

| depth `N` | baseline (KiB) | M-1 (KiB) |
|---|---|---|
| 100 | 824 | 784 |
| 200 | 1,592 | 1,496 |
| 400 | 3,108 | 2,912 |
| 800 | 6,144 | 5,752 |
| 1,600 | 12,220 | 11,428 |

All four series are linear with no curvature (pairwise slopes agree to <1.5%).

```math
\begin{aligned}
S^{\text{dbg}}_{\text{base}}(N) &= 197.5 + 47.257\,N &
S^{\text{dbg}}_{\text{M-1}}(N) &= 165.5 + 14.777\,N \\
S^{\text{rel}}_{\text{base}}(N) &= \phantom{0}69.0 + \phantom{0}7.595\,N &
S^{\text{rel}}_{\text{M-1}}(N) &= \phantom{0}75.2 + \phantom{0}7.096\,N
\end{aligned}
\qquad\text{(KiB)}
```

| profile | baseline B/level | M-1 B/level | factor | `D_max` @ 8 MiB |
|---|---|---|---|---|
| **debug** | 48,392 | **15,132** | **3.20×** (68.7% removed) | 169 → 542 |
| **release** | 7,777 | **7,266** | **1.07×** (6.6% removed) | 1,069 → 1,143 |

### 5.1 ★ M-1 is a DEBUG-PROFILE result, and the release numbers say why

The two profiles do not merely differ in scale — they disagree about whether the intervention
did anything:

* **debug**: 3.20×, 68.7% of the constant removed;
* **release**: 1.07×, 6.6% removed.

The explanation is the mechanism in §4, read in reverse. The arm-splitting removes cost only to
the extent that the compiler was *failing* to overlay mutually exclusive match arms. At
`-O0`/cranelift it fails completely, so the 89-arm frame really was the sum of 89 arms' locals
and hoisting them was worth 3.2×. At `opt-level = 3` **LLVM already performs that overlay**, so
there was almost nothing there to remove, and M-1 bought only the small residue.

This is corroborated by the debug/release ratio of the *baseline* itself: **6.2×**
(48,392 vs 7,777), collapsing to **2.1×** after M-1 (15,132 vs 7,266). M-1 did not make the
lowering cheaper in any deep sense; it made the **debug build stop paying a penalty the release
build never paid**.

Two consequences, and both matter more than the headline factor:

1. **The win is not worthless — debug is where this code is exercised.** The gate runs debug, CI
   runs debug, and every demo run sheet drives `target/debug/rholang`. Depth 169 → 542 in the
   profile a presenter actually uses is a real improvement, and it is what let the run-sheet
   prefixes come off (§7).
2. **★ Release is where the STRUCTURAL cost is visible, and it is 7,266 B/level — essentially
   untouched.** That residue is the genuine per-level frame of the 19-member SCC of §4.1: real
   locals in real functions, not a codegen artifact. It is what M-2 has to remove, and the
   release profile is the honest measure of M-2's success. A debug-only reading of M-1 would
   have suggested the problem was two-thirds solved; the release reading shows the structural
   problem is essentially entirely still there.

### 5.2 ★ SCOPE: the binary's slope is not the lowering's slope

Two instruments are used in this document and they measure **different scopes**. Conflating
them would make M-2 look like a bigger win than it is. Release profile, B/level:

| measurement | scope | B/level |
|---|---|---|
| gate `lower_depth` | the lowering, alone | 2,157 |
| gate `parse_depth` | the parser, alone | 304 |
| gate `reproducer` | parse + lower + **iterative** teardown | 2,128 |
| `bisect_ulimit` on `target/release/rholang` | **everything on the main thread** | **7,266** |

`reproducer` ≈ `lower_depth`, so parsing and lowering do not sum — the deeper of the two
dominates. But the binary costs **~5,100 B/level more than parse + lower together**, and that
residue is neither of them. It is the work the gate deliberately excludes so that each subject
measures one traversal: **rendering the observation**, and the **derived, recursive `Drop` of
the deep `Par`** (every gate subject avoids the latter via
`models::rust::rholang::par_children::dismantle`).

★ **Consequence, stated before it surprises anyone: M-2 will take the gate's lowering subjects
to zero without taking the binary to zero.** Converting the SCC removes its ~2,100 B/level; the
renderer and the `Par` teardown are separate traversals, also on the main thread, and each needs
its own conversion and its own gate subject. "The lowering is fixed" and "`rholang` is
depth-independent" are different claims, and only the first is M-2's.

---

## 6. ★ M-6 — the parser, measured (and a retracted claim)

The parse path had never been measured on this axis. "Not measured" must not be allowed to
read as "not present", so it was measured, on both axes, with explicit thread stack sizes.

### 6.1 The first measurement, and why it was wrong

The first ladder ran at parameters 16, 32, 64 and 128, and read **471,040 bytes at every
rung on both axes** — identical to the byte. The conclusion drawn was "slope 0, the parser is
not a member of this family".

**That conclusion was wrong.** It was retracted within the hour by the very gate this audit
introduces, which bisects at *both ends of a wide ladder* rather than sampling a narrow one.

### 6.2 What is actually there

| depth | min stack (B) | pairwise B/level |
|---|---|---|
| 128 | 471,040 | — |
| 256 | 499,712 | 224 |
| 512 | 815,104 | 1,232 |
| 1,024 | 1,536,000 | 1,408 |
| 2,048 | 2,977,792 | 1,408 |
| 4,096 | 5,861,376 | 1,408 |

The asymptotic slope is **1,408 B/level**, stable to the byte across the last three intervals.
Growth is flat to depth ≈ 256 and linear thereafter; the mechanism behind the knee is not
established here and is deliberately not guessed at.

The **width** axis is genuinely flat — 471,040 B at width 16, 32, 64, 128, 256, 1,024 and
4,096, a 256× range with slope **0**.

### 6.3 ★ The methodological lesson

The 471,040 B floor is the parser's **own** fixed intercept (~460 KiB of generated recognizer
tables and driver frame), not an artifact of the harness: the cheapest subject in the same test
binary, `lower_width`, bisects to 98,304 B.

§8 of this document, and the gate's own module header, warn that *a large intercept with a
small slope passes a fixed-stack ladder while still being Θ(depth)*. The retracted claim is
that hazard's **dual**: a large intercept with a small slope also reads as **zero slope** on a
ladder that never leaves the intercept-dominated regime.

```
        min stack
            ▲
            │                                          ╱ slope 1,408 B/level
   5,861 KiB┤                                       ╱
            │                                    ╱
            │                                ╱
   1,536 KiB┤                            ╱
            │                        ╱
     815 KiB┤                    ╱
     471 KiB┤━━━━━━━━━━━━━━━━╱                ← intercept-dominated: the FIRST ladder
            │  16  64 128  256   512   1024   2048   4096      lived entirely in here
            └──────────────────────────────────────────────▶ depth
               ╰── reads as "slope 0" ──╯
```

**Rule adopted for every slope measurement in this family:** both probe points must sit clear
of the subject's own floor, or the derived slope is understated — here, all the way to zero.
The parser tripwire is accordingly probed at 512 and 4,096, not at the 16 and 128 that produced
the retracted claim.

### 6.4 Disposition

The parser is Θ(depth) at 1,408 B/level, but it was never the binding constraint: 10.7× cheaper
per level than the M-1 lowering (15,132) and 34× cheaper than the original (48,392). It sits in
`parser_theta_depth_tripwire` with a ceiling at ~1.5× measured, and the width axis sits in
`parsing_is_width_independent`.

⚠ The claim in the M-5/M-6 commit message that the parser measures "0 B/level" on the depth
axis is **superseded by this section**. It is left in the history rather than rewritten, because
the retraction is part of the record.

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

**Deficit invariant**, asserted at the head of the drive loop behind `debug_assert!`. Let `V` be
the value stack, `D` the number of `Enter` items in the work stack, and `C` the set of pending
`Combine` items:

```math
|V| \;+\; D \;+\; |C| \;-\; \sum_{k \in C}\mathrm{arity}(k) \;=\; 1 .
```

⚠ An earlier form of this invariant, `|V| + D = 1 + \sum \mathrm{arity}`, is **wrong**: it is off
by `|C|` and fires immediately after the root descends. The corrected form is verified
transition-by-transition below — every reachable configuration, not a spot check.

| # | configuration | `\|V\|` | `D` | `\|C\|` | `Σ arity` | total |
|---|---|---|---|---|---|---|
| 0 | initial: `work = [Enter(root)]` | 0 | 1 | 0 | 0 | **1** ✓ |
| 1 | after `Enter` of an `n`-ary node: pop the `Enter`, push `Combine(k)` with `arity(k) = n`, push `n` `Enter`s | 0 | `n` | 1 | `n` | **1** ✓ |
| 2 | after `Enter` of a leaf (`n = 0`): pop the `Enter`, push one value | +1 | −1 | 0 | 0 | **1** ✓ |
| 3 | after `j` of those `n` children have resolved | `j` | `n − j` | 1 | `n` | **1** ✓ |
| 4 | all `n` resolved | `n` | 0 | 1 | `n` | **1** ✓ |
| 5 | after `Combine(k)`: pop `n` values, pop the `Combine`, push one value | `n − n + 1` | 0 | 0 | 0 | **1** ✓ |
| 6 | final: work empty, exactly one value | 1 | 0 | 0 | 0 | **1** ✓ |

Rows 1–5 are the only two transition shapes `δ` has, in their general form, so the table is
exhaustive over reachable configurations rather than illustrative.

⚠ **Maintain it with incremental counters, not an O(n) rescan.** `D`, `|C|` and `Σ arity` are
each updated by a constant on every push and pop, so the assertion is `O(1)` per step. A rescan
would make the debug build `O(n²)` on exactly the deep terms the gate gives it — the gate
bisects at depth 4,096.

`arity` is written as an exhaustive `match` over `Kont`, deliberately duplicating the pop counts,
because the point is to cross-check them against an independent statement. This fires on the
first malformed configuration on **any** term, whereas a differential fires only if the corpus
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

### 8.3 ⚠ Not members of this family

Two candidates were examined and **excluded on evidence**. They are recorded here so that
"not converted" is never later mistaken for "not examined".

#### PAR01 — a static constant, not a growth axis

`prattail/src/lint/lints.rs:5193`'s `max_depth` walks the **category reference digraph** with
cycle cutting. Its value is bounded by the number of categories and fixed at grammar-compile
time: it measures a static constant, not growth in input nesting. Useful codegen hygiene and
nothing more.

#### The "ambiguity nesting" axis — bounded by 2, and therefore not an axis

`collect_proc_alternatives` (`rholang_ast.rs`) recurses over
`RholangTermInner::Ambiguous(Vec<RholangTermInner>)`, which *looks* like a third growth axis
alongside depth and width. It is not: on any parser-produced term its recursion depth is
**bounded by 2**, because `Ambiguous` is flat by construction. Three independent mechanisms
enforce that, and all three were read rather than assumed:

| # | mechanism | location |
|---|---|---|
| 1 | **construction flattens one level** — `from_alternatives` opens with `alts.into_iter().flat_map(\|a\| match a { Self::Ambiguous(inner) => inner, other => vec![other] })`, which maintains flatness inductively | `macros/src/gen/runtime/language.rs:659` |
| 2 | **the generated type declares it** — *"Multiple parse alternatives (2+, flat — no nested Ambiguous)"* | `target/generated/rholang/term_wrapper.rs:31` |
| 3 | **four `unreachable!` guards assert it** at the `all_alts()` seams — *"all_alts() returns flat alternatives, not nested Ambiguous"* | `macros/src/gen/runtime/dovetail_report.rs`, `dovetail_report/typed_report.rs` |

So no gate subject was built for it and no ladder was measured: there is no slope to find, and
a subject that measured one would be measuring a shape no parser emits.

`Ambiguous` is nonetheless a public variant that a caller *can* nest by hand — the Calculator
test suite does exactly that — so the walk stays **total** rather than asserting flatness.

★ It was converted to an explicit work stack anyway, in its own commit, and the commit says
plainly that this is a **consistency fix and not a depth fix**. The justification is
independent of this audit: every *macro-generated* traversal over the same variant (`Clone`,
`Hash`, `PartialEq` in `macros/src/gen/runtime/language.rs`) already uses an explicit work
stack, and says so — *"no compiler-generated recursion through nested Ambiguous trees. Per the
stack-safety mandate."* `collect_proc_alternatives` was the last hand-written exception to a
mandate the generated code already honours. Removing an exception is worth doing on its own
terms; letting it borrow the depth work's justification would have inflated both.

Order is load-bearing in the conversion and is pinned by a differential test against the
retained recursive implementation
(`iterative_alternative_collection_matches_the_recursive_walk`): `lower_proc_alternatives`
dedups by semantic key with `BTreeSet::insert`, which keeps the **first** occurrence, so a
different visit order could retain a different representative.

---

## 9. ★ M-2 — LANDED, and what it did and did not move

Commit `3c0c3585`. The whole 87-member component of §4.1.1 is driven by one explicit
`Job`/`Kont` worklist (`rholang_ast::drive`), in the idiom of `prattail/src/sppf_realize.rs:164`.
The recursive form is retained VERBATIM under `cfg(test)` in
`rholang-runtime/src/rholang_ast/recursive_oracle.rs` and compared against the driver by five
differentials (byte-identical encoded `Par`, identical typed errors, identical side registers,
over 97 surface-syntax entries plus a depth-400 term, with all 31 continuations asserted reached).

### 9.1 ★ The instrument changed, and the old one was measuring a proxy

Every number below is a **direct bisection of `RLIMIT_STACK`, installed in a forked child before
`exec`, with the subject running on that child's MAIN thread**. The gate's previous probe ran each
subject on a `std::thread::Builder::stack_size` thread. That is precise but it is not the thing:
a spawned thread's stack is one `mmap` with a guard page; a main thread's is a kernel-grown VMA
bounded by the rlimit, and §1.1 is the whole reason it is the latter that production faults on.

The probe therefore had to stop being a `#[test]`, for a mechanical reason: **libtest runs every
test on a spawned thread**, so a `#[test]` body cannot execute on a main thread whatever the
parent sets. It is now `rholang-runtime/src/bin/stack_depth_probe.rs`, a program whose `main`
runs the subject directly.

Two independent cross-validations say the instruments agree where they overlap: `parse_depth`
bisects to **1,408 B/level**, reproducing §6.2 to the byte; and the pre-M-2 release binary
bisects to **7,277 B/level** against §5's least-squares 7,266 — 0.15%.

### 9.2 The lowering

B/level, bisected 16 → 4,096 (width subjects 4 → 65,536):

| subject | traversal | debug | release |
|---|---|---|---|
| `lower_leak` | the lowering ALONE — both teardowns removed | **0** | **1** |
| `lower_depth` | `CastList` ⇄ `lower_list` (the reproducer's path) | **1** | **0** |
| `lower_add` | the binary-expression cycle | **0** | **0** |
| `lower_par` | `PParInfix` — recurses on BOTH operands | **1** | **0** |
| `lower_neg` | `Int::NegInt` ⇄ `lower_int_value` (§4.1.2) | **0** | **1** |
| `lower_width` | sibling count | **1** | **0** |
| `lower_new` − `new_build` | the `PNew` arm, minus its own builder | **1** | **0** |

A reading of 0 or 1 B/level is one 4 KiB bisection bucket across a 4,080-step ladder — the
instrument's floor. Several readings are NEGATIVE before clamping, which is what a flat subject
looks like when address-space layout shifts by a bucket. Against §5.2's pre-M-2 release
`lower_depth` of 2,157 B/level, the class is gone.

### 9.3 ★ ANTI-VACUITY changed a conclusion here, and the record should say so

`lower_depth` FIRST read **252 B/level**, and the obvious reading — "the conversion is
incomplete" — was wrong. `ast_drop`, a subject that builds the identical term and lowers
*nothing*, read **254**. The slope was the AST's own teardown, and it had been inside every
lowering subject all along because the gate `drop`ped the input term.

The discriminator is `lower_leak`: build, lower, `mem::forget` both sides. It reads 0. The rule
§6.3 adopted for probe POINTS ("both must clear the subject's own floor") has a companion for
probe SUBJECTS: **a subject that contains two traversals measures neither**, and the only way to
know which one a slope belongs to is to build the subject that contains one of them.

The gate's earlier claim that a plain `drop(term)` is correct here — on the grounds that the
`language!` macro emits a pooled iterative `Drop` — is **superseded**. It is true of a pure
`Proc` chain and false across a type hop; see §9.4.

### 9.4 ★ THE RESIDUE — every Θ(depth) traversal still on the main thread

| subject | traversal | owner | debug | release |
|---|---|---|---|---|
| `par_drop` | `drop_in_place::<Par>` — `prost`'s DERIVED recursive `Drop` | `models` (f1r3node) | 368 | 95 |
| `ast_drop` | the `language!` iterative `Drop`, ACROSS a cross-type hop | `macros/src/gen/` | 271 | 96 |
| `render` | `observation::render_par_text` — decode + format | this crate | 3,665 | 911 |
| `lower_formula` | `formula::is_statically_false` ⇄ `is_statically_true` | `languages/src/` | 4,094 | 978 |
| `parse_depth` | the WPDA parser (§6) | `prattail` | 1,408 | 303 |

★ **The two `Drop`s belong to the DERIVED-IMPL class and are not reachable by the pushdown
transform this audit specifies.** A pushdown transform rewrites a traversal *whose text you own*
into a worklist. `drop_in_place::<Par>` has no text: it is glue the compiler derives from the
type, and the only repairs are to change the type or to intercept at the call site. f1r3node's
`par_children::dismantle` IS that call-site interception, which is why `par_drop` — the one
subject that deliberately does not use it — is the only one still paying.

`ast_drop` is the same class with a twist worth recording: the macro **does** emit a pooled
iterative `Drop`, and `lower_add` (a pure `Proc::Add(Arc<Proc>, …)` chain) is flat under it. But
`nested_list` alternates `Proc::CastList(Arc<List>)` with `List::ListLit(Vec<Proc>)`, and the
worklist does not follow the hop through `List`. The generated teardown is iterative *within* a
type and recursive *across* types.

`lower_formula`'s slope is **not** the formula compiler — that was converted, and
`Job::Formula`/`Kont::Formula*` drive it from the same work stack. It is the syntactic
static-falsity judgement `lower_proc`'s `Matches` arm consults *before* lowering, a mutually
recursive pair in another crate.

### 9.5 ★ The whole binary — and a superseded attribution

`ulimit -s` bisection of `rholang` on a `nest-d.rho` ladder at `d` = 100 and 400,
`RUST_MIN_STACK` pinned to 1 GiB so only the main thread binds:

| profile | before (M-1) | after (M-2) | factor |
|---|---|---|---|
| release | 7,277 | **2,567** | **2.83×** |
| debug | 15,132 *(§5, reproduced)* | **15,155** | **1.00×** |

The release result is the expected one: the lowering was the binding main-thread traversal, and
removing it leaves the residue of §9.4. `D_max` on the 8 MiB default rises from ~1,140 to ~3,260.

★ **The debug result is a finding, and it supersedes §5's attribution.** Minimum stack is a
`max` over the deepest single path, not a sum over traversals — parsing, lowering, rendering and
teardown run *sequentially*. Removing the lowering entirely left the debug binary's slope
unchanged at 15,155, so **the lowering was never the binding main-thread traversal in the debug
build**; something else costs ~15,150 B/level there and always did. §5 recorded 15,132 as "the
M-1 lowering", and that is now known to be a coincidence of magnitude rather than an attribution:
the gate's debug lowering subjects read 0.

The residues of §9.4 sum to ~5,700 B/level in debug, so ~9,400 B/level of the debug binary's
main-thread cost is **still unattributed**. The likely candidate — f1r3node's normalizer /
`substitute` / sort running on the main thread before the reduction is handed to tokio — is
named as a candidate and deliberately **not** claimed: it has not been measured, and this
document's standard is that an unmeasured mechanism is written down as a question.

---

## Appendix A — reproducing the measurements

The probe program, at nesting depth `d`:

```bash
{ printf '@"OUT"!('; for ((i=0;i<d;i++)); do printf '['; done; printf '1';
  for ((i=0;i<d;i++)); do printf ']'; done; printf ')\n'; } > nest-$d.rho
```

Minimum viable `ulimit -s` at a fixed depth (exponential probe, then bisect to 4 KiB):

```bash
runs() { ( ulimit -c 0; ulimit -s "$1"; exec target/debug/rholang "$2" >/dev/null 2>&1 ); }
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
cargo test -p rholang-runtime --features "rholang-runtime lambda-runtime calculator-runtime" \
  --test stack_depth_gate -- --ignored --exact report_slopes --nocapture
```

---

## Appendix B — status

| step | state | measured |
|---|---|---|
| instruments + baseline | ✅ | 48,392 B/level; `D_max` 169 (main) / 132 (default) |
| threshold reconciliation | ✅ | §2.1 |
| SCC enumeration | ✅ | §4.1 — 19 members; **re-derived 87** after M-1 — §4.1.1, method §4.1.2 |
| M-1 per-arm split | ✅ landed | debug 15,132 B/level (3.20×); release 7,266 (1.07×) — §5.1 |
| M-2 explicit-stack driver | ✅ landed `3c0c3585` | lowering **0 B/level**, both profiles — §9.2 |
| M-3/M-4 `collect_proc_alternatives`, ambiguity-nesting axis | ✅ | §8.3 — bounded by 2, no axis |
| M-8 the residue (`par_drop`, `ast_drop`, `render`, static falsity) | ☐ outstanding | §9.4 — each has a gate subject and a number |
| M-9 the debug binary's unattributed ~9,400 B/level | ☐ open question | §9.5 |
| M-5 gate | ✅ landed | tripwire + width axis green |
| M-6 parser probe | ✅ | depth 1,408 B/level (asymptotic); width 0 B/sibling — §6 |
| M-7 run-sheet prefixes | ✅ landed | 13 demos green at the default stack |
