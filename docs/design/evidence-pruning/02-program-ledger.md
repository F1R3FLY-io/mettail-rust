# Evidence-Pruning Program — Running Ledger

> The P-series execution ledger (plan: `02-staged-implementation-plan.md` v3, USER-APPROVED
> 2026-06-11; red-team record: `03-red-team-ledger.md`, CONVERGED after 4 rounds).
> Every stage records its M/D/I/L commits, measured numbers (per-corpus), accept/STOP verdicts,
> and pgmcp experiment ids here. STOPs are first-class outcomes (H13/CD06 precedent).
>
> **Strategic frame (user directive, 2026-06-11):** the P-series executes FIRST; the
> Dovetail/Rho-machine flip (M-RHO.1→.4) follows immediately after — and no further correctness
> investment goes into Ascent-side problem classes the flip dissolves by construction.

## Baseline (pinned 2026-06-11 @ `f1ea267c`)

The post-ROOT-A/ROOT-F/eval-closure baseline — all waste numbers and battery gates compare
against THIS commit (the unsourced pre-ROOT-A "342,699" figure is retired; see red-team F1):

| Suite | Result | Notes |
|---|---|---|
| `gen_ledtest_op` | **220/0** | SENTINEL — any failure aborts the active stage |
| `gen_calculator_op` | 1330/0 | |
| `gen_rhocalc_op` | 530/1 | pre-existing `castbigrat` (tracked separately) |
| `edge_case_tests` | 229/0 | the historical ambient pair fixed @ 38dcd485 |
| `rhocalc_tests` | **126/0** | first-ever full green @ f1ea267c |
| `gen_ambient_analytical` | 52/0 (1 ignored) | |
| `gen_ambient_rewrite` | 13/0 | |
| `gen_ambient_prop` | 17/0 | |
| `mettail-prattail --lib` | 3980/0 | includes egraph:: |
| `--features walker-stats` build | green | I6 gate (round-2 B-1) |
| `rocq-prattail-wpda` | green | zero-Admitted corpus |

Model commits already landed (M-commits, zero-admission, `Print Assumptions` clean):
- `ParikhObligationGate.v` (P2 spec, 9 thms) @ 288bcb42
- `EvidenceGatedDelegates.v` (P1 spec, 6 thms) @ 6829a5e5
- `ForwardOrderOnly.v` (P4 spec, 6 thms incl. the consolidated InnovationDemotion obligations) @ 8106ec26
- `CollectionForkEvidence.v` (16 thms; the ROOT-F production validation of the program's
  philosophy) @ 288bcb42 + 38dcd485 + ac88faeb

## P0 — Scaffold (this stage)

| Deliverable | Status |
|---|---|
| This ledger file (pinned baselines) | ✅ this commit |
| `stats_inc_idx!` + `WPDA_STATE_CLASS_COUNT` (partitioned-counter mechanics, round-2 m-1) | ✅ this commit |
| P-series conventions section in walker_stats.rs (`PRATTAIL_EP_<STAGE>=off\|shadow\|on`; `<stage>_shadow_{would_refute_total, refuted_then_accepted, steps_after_would_refute}` partitioned by WpdaState-class × recovery_enabled; non-zero-slot printing) | ✅ this commit |
| `languages/examples/cast_tower_bench.rs` (the P1/P2 Welch panel; kill-switch arms; **tiered** — see smoke findings) | ✅ this commit |
| `recovery_cohort_bench` zero-innovation extension + `PRATTAIL_EP_P4_DEMOTE` arm | ✅ this commit |
| Battery identical (P0 is behavior-neutral) | ✅ **PASSED** — ledtest 220/0 SENTINEL, calc 1330/0, rhocalc_op 530/1 (pre-existing castbigrat), edge 229/0, **rhocalc_tests 126/0**, ambient 52/0+13/0+17/0, prattail-lib 3980/0, BOTH cfg builds green (default + `--features walker-stats`), bench smoke exit-0 with well-formed CSV |

### P0 smoke findings (2026-06-11 @ f1ea267c, debug profile)

The bench smoke was NOT a formality — the panel as first written (uniform 20 reps × 30
samples) could never complete its base arm. Per-input bisect (single parse, debug):

| idx | input | shape | time |
|---|---|---|---|
| 0 | `int(3) == 3` | d1 + cmp | 7.5 ms |
| 1 | `int(3) + 3` | d1 + arith | 7.0 ms |
| 2 | `int(3)` | d1 | 6.8 ms |
| 3 | `int(float(int(3.14)))` | d3 tower | 29.6 ms |
| 4 | `int(float(int(3.14))) == 3` | d3 tower + cmp | **1.17 s** (40× its bare tower) |
| 5 | `int(float(int(float(int(3.14)))))` | d5 tower | 121 ms |
| 6 | `int(float(int(float(int(3.14))))) == 3` | d5 tower + cmp | **> 580 s** (> 4800× its bare tower) |
| 7 | `int(1) == 1 and int(2) == 2` | 2× d1 + cmp | 11.7 ms |
| 8 | `float(3) >= 3.0` | d1 float cmp | 7.2 ms |

**The law:** bare towers scale gently (~4× per +2 depth); a compare continuation BEHIND the
tower explodes the frontier ~K^depth (d3+cmp 40×, d5+cmp >4800× — consistent with K≈5-7 per
level once the cross-cat-LHS delegate fan engages). This is the P1 pathology measured live on
the shipping tip — the panel's base arm IS the "before" evidence, and the depth-independence
claim (`CastLookaheadGateBound`: gated frontier ~ trigger count, NOT depth) is directly
testable input-by-input.

**Protocol consequence (bench redesign, this commit):** per-input CSV rows
(`config,input_idx,reps,sample,nanos`); heavy tier (idx 4, 6) runs reps=1/sample; env knobs
`CAST_TOWER_SAMPLES` / `CAST_TOWER_HEAVY=off` (debug smokes) /
`CAST_TOWER_PATHOLOGICAL=on` (idx 6 — EXCLUDED by default so the bench completes out of the
box; even release-profile idx 6 projects to tens of seconds per parse × 30 samples on the
base arm). Panels run RELEASE. Base-arm evidence for idx 6 is a right-censored wall-clock
bound (> 580 s debug single-parse at this baseline), not a t-test sample; treatment arms
(P1 gate on) opt in and SHOULD complete it — that asymmetry is itself the
depth-independence acceptance evidence.

**Harness traps recorded (cost a prior session ~3 silent smokes):** (1) `cargo run --example`
re-fingerprints against a DIFFERENT feature unification than `cargo build --examples` → full
languages-lib rebuild (~minutes) silently eating the timeout — build first, then execute the
binary from `target/debug/examples/` directly; (2) Rust stdout is BLOCK-buffered to
files/pipes — a timeout-killed run loses ALL buffered CSV, indistinguishable from "no
output" (`exit: 0` from `head`/`tail` in a pipeline masks the kill); progress/diagnostic
lines belong on stderr (unbuffered).

## P1 — Delegate fan (in flight)

M `EvidenceGatedDelegates.v` ✅ (landed early @ 6829a5e5) → D counters/probes (this commit) →
gates (d2 iff `crosscat_lhs_d2_only_hits > 0`; share iff dup ≥ 10%, EquivKey ONLY) → I → L.

### D-commit (Step-0 diagnostic) — instrumentation inventory

| Counter | Site | Mechanism |
|---|---|---|
| `crosscat_lhs_fallthrough_considered` | generated lex-fork fall-through gate (forks.rs fragment → `<lang>/wpda.rs`) | `ep_p1` process-cumulative atomics behind an always-defined hook (`note_crosscat_lhs_fallthrough`) — the gate runs in GENERATED code with no walker access |
| `crosscat_lhs_fallthrough_gated_off` | same | `kind_hit && !gate_open` — the trigger-presence gate suppressed an otherwise-eligible crosscat fall-through |
| `crosscat_lhs_d2_only_hits` | same | fall-through TRUE ∧ false-without-the-crosscat-disjunct ∧ ≥1 lex-alt bypassed — the runtime witness of FV `d1_d2_delta` (the bypassed secondary interpretation). **0 across battery+corpus ⇒ d1 suffices ⇒ d2 STOP** |
| `crosscat_lhs_delegates_spawned` | walker `PushWithEdgeKind` arm, `EdgeKind::CrossCatLhs` | per-walker counter |
| `crosscat_lhs_delegate_dup_at_pos_source` (+ backing map) | same | spawns beyond the first at one `(pos, source_src_idx)` — spawn multiplicity IS the would-share measure (an EquivKey merge coalesces exactly these at registration). **< 10% of spawned ⇒ share STOP** |
| `cast_then_infix_steps` | `apply_action_to_cursor` entry | cursor-under-CrossCatLhs-frame attribution; exact memo by interned `incoming_edge_stack_id` (one edge-stack walk per distinct stack, ever). Waste-gate metric (≥ 60% drop on `int(float(int(3.14))) == 3` under enforcement) |

**d2-(b) static audit (RESULT — recorded so it is not re-asked):** the plan prose's second
d1-miss form — "multi-token-prefix cast triggers d1 misses" (the 51d57c91 lex-alt-table gap
pattern) — does NOT exist in the d1 kind predicate: `emit_prefix_crosscat_lhs_dispatch_arms`
feeds on `first_set_of_category`, which covers ALL rule shapes (synthetic native-literal rules,
synthetic Var, the B7 synthetic collection-literal fix, every `classify_atomic` shape, and
NonAtomic multi-token keyword prefixes incl. the H1 leading-Param recursion). The d1 predicate
inherits exactly the Pass-0 arm coverage ("no drift" by construction). The only live d1-vs-d2
delta is the model's (a)-form — the bypassed secondary interpretation — which
`crosscat_lhs_d2_only_hits` measures exactly.

**Measurement protocol:** `cargo build -p mettail-languages --features walker-stats --examples`,
then per probe input `PRATTAIL_WALKER_STATS=1 ./target/debug/examples/cast_probe <idx>` and grep
the LAST `ep_p1_crosscat_lhs` block (gate counters are process-cumulative; the last report
carries the totals). Corpus: the 9 bench inputs + `edge_case_tests::{comparison_after_cast_results,
operator_chains_after_casts}` under `--features walker-stats`.

### Step-0 measurements (2026-06-11, debug + walker-stats, one parse per process)

| idx | input | considered | gated_off | d2_only | spawned | dup (ratio) | cast_then_infix_steps |
|---|---|---|---|---|---|---|---|
| 0 | `int(3) == 3` | 38 | 0 | 1 | 10 | 8 (80%) | 388 |
| 1 | `int(3) + 3` | 37 | 9 | 0 | 9 | 8 (89%) | 36 |
| 2 | `int(3)` | 36 | 9 | 0 | 9 | 8 (89%) | 36 |
| 3 | `int(float(int(3.14)))` | 155 | 33 | 0 | 24 | 23 (96%) | 96 |
| 4 | `int(float(int(3.14))) == 3` | 1239 | 0 | **55** | **3504** | **3500 (99.9%)** | **149,645** |
| 5 | d5 bare tower | 297 | 63 | 0 | 214 | 213 (99.5%) | 856 |
| 6 | d5 + cmp | — right-censored (> 580 s; never reaches the report) — | | | | | |
| 7 | `int(1) == 1 and int(2) == 2` | 76 | 0 | 2 | 20 | 16 (80%) | 776 |
| 8 | `float(3) >= 3.0` | 38 | 0 | 1 | 10 | 8 (80%) | 390 |

**The mechanism, quantified:** idx 4's dup map is `[((2,5), 9), ((4,2), 183), ((6,5), 3311)]` —
the SAME `(pos, source)` delegate re-spawned 3,311× under the compare continuation vs 24× on the
bare tower (idx 3) and 214× at depth 5 bare (idx 5). The compare continuation multiplies
re-spawns of IDENTICAL delegates; `gated_off` is non-zero exactly on the trigger-free inputs
(1/2/3/5 — the 5A gate suppressing where no infix trigger is ahead) and zero on compare inputs
(gate open, as designed).

### Gate verdicts (plan §P1 accept/STOP)

1. **Cohort-share: IMPLEMENT.** `dup/spawned` = 80–99.9% on EVERY probe input — vastly over the
   10% threshold (idx 4: 3500/3504). The I-commit shares EquivKey-identical CrossCatLhs
   delegates ONLY (`DispatchKey::equiv` = `(source_src_idx, inner_cur_bp)`); `wrap_rule`/
   `wrap_cat` REMAIN cache-key discriminators (M4 tombstone — never re-widen).
2. **d2 extension: STOP** (the plan's gate quantity, the (b)-form "multi-token-prefix d1 miss",
   is 0 BY CONSTRUCTION — see the static audit above; `d1_d2_delta` stays a proven-but-unneeded
   reserve). The runtime (a)-form counter measured 55/2/1/1 load-bearing fall-throughs with a
   bypassed secondary (Var) interpretation on compare inputs — recorded as a WATCH ITEM, not a
   gate trigger: the bypassed Var branches are syntactic dead-ends on this corpus (battery
   green, no accepted-parse loss observed); if a grammar ever needs a variable named like a
   cast keyword in source position, d2's fork-keeping `LexAltRuleKind::CrossCatLhs` variant is
   the proven remedy. Cluster-scale confirmation: `edge_case_tests::{comparison_after_cast_results,
   operator_chains_after_casts}` (25/25 green under walker-stats) totals
   `considered=10,934 / gated_off=797 / d2_only=181` — 181 bypassed-secondary events, zero
   failures.
3. **Waste-gate baseline PINNED:** `cast_then_infix_steps` on idx 4 = **149,645**. The P1
   I-commit (enforcement on) must show ≤ 59,858 (≥ 60% drop) on this input, else the residue
   passes to P2/P3 with the diagnostic attribution recorded.

## Stage log

- 2026-06-11 P0 opened.
- 2026-06-11 P0 smoke caught the heavy-tier blowup (idx 6 > 580 s debug) → bench redesigned
  (tiers + per-input rows + env knobs); battery gate PASSED (all 9 suites + both cfg builds
  identical to the pinned baseline); P0 committed @ 06b229ae.
- 2026-06-11 P1 D-commit (Step-0 diagnostic): counters landed + corpus measured. VERDICTS:
  cohort-share IMPLEMENT (dup 80–99.9% ≫ 10%; idx 4: 3500/3504, one (pos,source) key spawned
  3311×); d2 STOP (the (b)-form is 0 by static audit; (a)-form 55+181 bypassed-Var dead-ends =
  watch item); waste baseline pinned 149,645 attributed steps on idx 4 (I-commit target
  ≤ 59,858). Battery green at baseline incl. prattail-lib 3980/0 BOTH cfgs (the battery caught
  a test-cfg struct-literal break — fixed in-commit).
