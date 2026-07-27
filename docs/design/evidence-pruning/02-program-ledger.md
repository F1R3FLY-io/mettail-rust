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
| `gen_rholang_op` | 530/1 | pre-existing `castbigrat` (tracked separately) |
| `edge_case_tests` | 229/0 | the historical ambient pair fixed @ 38dcd485 |
| `rholang_tests` | **126/0** | first-ever full green @ f1ea267c |
| `gen_ambient_analytical` | 52/0 (1 ignored) | |
| `gen_ambient_rewrite` | 13/0 | |
| `gen_ambient_prop` | 17/0 | |
| `prattail --lib` | 3980/0 | includes egraph:: |
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
| Battery identical (P0 is behavior-neutral) | ✅ **PASSED** — ledtest 220/0 SENTINEL, calc 1330/0, rholang_op 530/1 (pre-existing castbigrat), edge 229/0, **rholang_tests 126/0**, ambient 52/0+13/0+17/0, prattail-lib 3980/0, BOTH cfg builds green (default + `--features walker-stats`), bench smoke exit-0 with well-formed CSV |

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

**Measurement protocol:** `cargo build -p languages --features walker-stats --examples`,
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
   **R7-8 Step-0 RE-PIN (2026-06-12, widened memo incl. `CrossCatLhsReentry`):** idx 4 OFF =
   **149,645 — unchanged** (the +cmp flows' reentry-window work was already attributed under
   outer tower frames), so the **≤ 59,858 target stands** under the widened predicate. Bare
   towers gained as expected (idx 3: 96 → 144; idx 5: 856 → 1,284 — EOI unwind under Reentry
   frames now counted); idx 0/7 unchanged (388/776). The ON arm now measures the same
   semantic class — the rename-artifact trap is closed.

### Round-5 red-team + §P1 AMENDMENT (2026-06-11, user-approved)

The I-commit design v1 (04-p1-icommit-design.md, cohort-cache producer) was red-teamed by 2
independent critics → **CONVERGED on REDESIGN** (full record: 03-red-team-ledger.md Round 5,
R5-1..R5-9). Headline refutations: the CrossCatProjection revive cannot be parameter-tweaked
into a CrossCatLhs revive (the member tail is predecessor-dependent: effective_new_state +
guarded reentry at hi_pos + F-1 splice-skip + D-strings re-sync); widening the COMPARED
`EdgeKind` can split GSS dedup with the switch OFF (grammar-conditionally inert only); the
=on measurement as specified was not apples-to-apples. Round 5 also exposed the deeper fact:
**the I7 "no new merge machinery" premise (gate alone bounds the fan) is FALSIFIED by the
Step-0 data** — the duplicates are redundant-VIABLE cursors that neither the EquivKey merge
nor P2 refutation can remove; only cohort-style PARKING removes the measured class.
**USER DECISION: amend §P1 → parking v2** (recorded in 02-staged-implementation-plan.md §P1
amendment block): shadow half first → NEW Rocq model (M-commit, parking/revive semantics,
non-vacuous per R5-8) → design v2 with ALL R5 corrections → re-red-team to convergence →
implement → ≥60% waste gate with R5-4-corrected attribution.

### SHADOW half SHIPPED (this commit)

`PRATTAIL_EP_P1=off|shadow` (per-walker, read once at construction; `on` warns + runs shadow
until v2 lands). Observation-only would-share measurement at the `cursor_gss_push_with_kind`
chokepoint — catches BOTH producers (the Pass-0 singleton arm AND the lex-fork
PushCrossCatLhs route; **the D-commit's 3504 figure is singleton-arm-only by site** — on idx 4
the chokepoint total equals the arm total, i.e. ZERO fork-path spawns on that input). Key =
`(push pos, source, host_cat)` = the full DispatchKey modulo the per-arm-constant wrap_rule.
NEVER touches the dispatch-cohort cache (the Round-5 shadow-inertness contract); counters
`ep_p1_shadow_would_share_total` partitioned [state_class × recovery_enabled].

**Shadow measurements (idx 4, debug+walker-stats):** `would_share_total = 3500` — EXACTLY the
D-commit dup figure (the full-key cross-check critic A demanded: host_cat=7 is constant on
calculator, so the wrap discriminator splits nothing → v2 sharing can collapse the full
3,500). Full-key dups `[((2,5,7),9), ((4,2,7),183), ((6,5,7),3311)]`. All hits in partition
slot 0 (dispatch class, recovery-off). Off-mode control: zero shadow lines (inert ✓).

## P2 — Parikh/suffix-obligation gate (OPENED 2026-06-12)

M `ParikhObligationGate.v` ✅ (landed @ 288bcb42) → D Step-0 (suffix_classes.rs +
codegen must-tables + shadow counters + the two check sites; **lattice DAG-node masks ARE the
critical path** — M-1) → gates (refuted_then_accepted == 0 HARD everywhere;
steps-after-would-refute ≥ 20% of apply_action_calls ⇒ enforce, < 5% ⇒ STOP) → I (enforcement
at the two sites + the O(1) mask test replacing the trigger-ahead rescan as a separately
flippable sub-commit) → L (Welch). Corpus: the cast probes (incl. the idx4 ON residue of
11,962 attributed steps), ProcX root-fan, post-ROOT-A rholang send/receive, + the adversarial
INSERT/SUBSTITUTE/Optional-skip/multi-length-lex probes. Kill switch PRATTAIL_EP_P2
(off|shadow|on per the P0 convention).

### P2 Step-0 verdict (2026-06-12): **STOP — recorded, first-class (H13/CD06 precedent)**

D-commit SHIPPED (diagnostic substrate retained; enforcement NOT implemented per the gate):
`suffix_classes.rs` (linear + lattice-DAG backward DP, 8/0 tests both cfgs, injected class fn);
`parikh_tables.rs` codegen (calculator: 6 trigger classes + coarse = 7; 492 must entries;
**hand-checked**: EqInt (7,0,0)=72/(7,0,1)=72/(7,0,2)=64 == must(Int) ∪ {==} exactly);
EpP2Mode{Off,Shadow} + the three check sites + the D-4 lineage tripwire
(`BranchCursor::ep_shadow_refuted`, OR-merged, FrontierArc round-trip).

**MEASURED: would_refute = 0 across the ENTIRE corpus** (cast probes both ep_p1 states,
rholang_tests, ledtest_op, rholang_op); refuted_then_accepted = 0 (the tripwire never fired).
**The zero deep-dived to mechanism (D-5, not a bug):** the only trigger-bearing must entries
belong to INFIX comparison rules consumed via InfixLoop/InfixContinuation — the runtime never
pushes a RuleAt frame at the operator position; every frame that DOES surface carries ∅ or
always-satisfiable coarse obligations. The model's top-RuleAt-frame restriction (red-team F4 —
the SOUND O(1) choice) has zero empirical bite at this granularity on these grammars. Gate
capability proven LIVE (`ep_p2_gate_fires_iff_obligated_class_absent_from_suffix`: fires on
absent ==, silent on present ==, ∅ on non-RuleAt) — the zero is real, not vacuous.

**Verdict: 0% ≪ 5% ⇒ STOP** per the plan's own gate ("record; proceed to P3 diagnostics
anyway — A and B kill different classes"). Battery at baseline (SENTINEL 220/0; prattail-lib
3989/0 both cfgs incl. the 9 new tests; macros 367/0; shadow inert: =shadow edge 229/0 ==
default). Full record: /tmp/p2_step0/findings.md (transcribed into this repo's history via
this commit message).

## P4 — ESS + innovation demotion (CLOSED 2026-06-12: ESS KEEP / demotion STOP)

M `ForwardOrderOnly.v` ✅ (@ 8106ec26, unmodified — the binding scheduler contract; its
invariants respected: within-step-only reordering, every_member_stepped_before_exit,
ess_report_no_prune). Implementation shipped:
- **ESS (KEEP, always-on):** `frontier_ess_x1000` (Kish (Σw)²/Σw² over exp(−primary)
  likelihood mass), computed LAZILY at the 3 budget-sentinel sites + EOI only (zero hot-path
  cost), threaded sentinel → `WpdaResolveResult::AmbiguityBudget` → the generated
  ParseError hint — a budget overflow now reports "frontier ESS≈k of n", distinguishing
  1-winner+noise from genuine k-way ambiguity.
- **Demotion (STOP per the plan's own fallback; the switch stays as the documented dormant
  negative-result arm):** within-step stable-partition behind `PRATTAIL_EP_P4_DEMOTE`
  (default OFF; battery byte-identical both states; the `demoted_member_unstepped_at_exit`
  tripwire 0 across 14 reports with up to 472 demotions fired). The Welch panels
  (cast_tower_bench, recovery_cohort_bench) are ALL NEUTRAL — a complete parse steps every
  cursor regardless of order; no beam exists to benefit. DEEP-DIVED hazard (proven by AST
  flip): demote-ON perturbs the equal-weight tiebreak winner (CastBigInt → CastUInt32 on a
  10-way cast tie) ⇒ a **313× eval-side blowup** on `{get(put(map(),1,10),1)}` (0.5 s →
  156.9 s) — the parse is identical (apply_action_calls/step_fanout_calls OFF==ON); the
  receiver-on-merge-equality + EOI lex-min tiebreak is ORDER-SENSITIVE, which the model
  soundly abstracts by keying all fields. **Cross-reference for the Dovetail flip:** the
  order-sensitive equal-weight tiebreak is a latent nondeterminism a total content-derived
  extraction tiebreak dissolves by construction (the plan's own realize-side requirement).

## P6a/P6b — probes (CLOSED 2026-06-12)

- **P6a DV-0: GATE PASSES** — untouched-e-node share 93.1–95.8% (≥50% ✓); saturation
  82.2–84.1% of eval wall (≥20% ✓). Deep-dived ground truth: dovetail has NO live eval
  caller yet (M-E.0 inert; rholang-runtime runs RhoRuntime directly — dovetail is not
  even a Cargo dep there), so the corpus is the largest existing saturate→extract workload;
  the mechanism is robust (saturation materializes hundreds of equivalent e-nodes; exact
  1-best extraction touches ~14–18). **Disposition: DV-1 (demand-gated saturation,
  SaturationDemandGate.v) is RECOMMENDED and FLIP-ALIGNED — scheduled within the M-RHO
  epic; re-measure on the real corpus post-flip.** Probe: dovetail/src/rules.rs::dv0_probe
  (dovetail 40/0).
- **P6b EV-0: GATE FAILS on the merits AND superseded** — undemanded facts 0.0% (terms) /
  3.2% (rewrites) ≪ 50% (eval wall-share 47.8% ≥20% is moot): the #307 semantic-key dedup +
  canon-pair quotient already collapse the undemanded class before it surfaces, and the
  reduction-DAG shape makes every surviving term NF-reachable ("the parse→eval seam is
  sound today" — the contract's own anticipation). **EV-1 = NON-GOAL, doubly: the gate
  fails, and the user directive supersedes Ascent-side investment.** Probe:
  languages/examples/ev0_probe.rs. Caveat recorded: measured at the post-quotient surface
  (a conservative bound; the raw layer is precisely what the quotient collapses).

## ★ THE P-SERIES LADDER IS CLOSED (2026-06-12, 26 commits, P0 → P6)

P0 ✅ scaffold · P1 ✅ THE WIN (idx4 −47.3% p=1e-45; idx6 35×; default On; two deep-dive
true-root fixes) · P2 ⏹ STOP (mechanism: no RuleAt at operator positions) · P3 ⏹ STOP
(gate-fail 5.7× as predicted; the transition census = Dovetail substrate) · P4 ✅ ESS / ⏹
demotion STOP (the 313× tiebreak hazard = a Dovetail cross-reference) · P5 ⏹ STOP (0.0000%;
the work is consumed mid-parse by P1's parking) · P6a ✅ gate-pass → DV-1 flip-aligned ·
P6b ⏹ non-goal. Every verdict mechanism-derived; every STOP first-class. **The program's
residual waste classes live in the architecture the Dovetail/Rho flip replaces — the
strategic frame's prediction, now measured. NEXT: M-RHO.1.**

## EP POST-FLIP — DV-0′ (CLOSED 2026-06-17 @ HEAD 75d7c6df): DV-1 STOP, re-derived against Ambient

The 2026-06-12 DV-0 gate-pass (93–96% untouched) was a **1-best `kth` early-stop
artifact**. DV-0′ rebuilt the probe to the **production extraction shape** (constant-zero
weight + `collect_checked` full-stream, `dovetail_report.rs:735/739`) with a rigorous
set-difference over the saturation-added population, and added an **Ambient-faithful AC
workload** (real `par` bags + AcApp OpenRule) to satisfy the "re-derive against Ambient"
mandate.

**RESULT (gate: untouched ≥ 50% AND sat ≥ 20% eval-wall):**
- synthetic worst-case (commutativity+expander): production untouched **0.0%** (1-best
  reported 97–99% — the artifact); collect_checked cross-check == reachable == added.
- Ambient AC (OpenRule over `par` bags): `added(sat)` tiny (**4 / 9 / 17** for 3/8/16
  redexes ≈ 1 node/redex — the canon-bag dedup gate working), production untouched
  **25% → 11% → 6%** (trending to 0 at scale).
- Every figure ≪ 50% ⇒ **GATE FAILS ⇒ DV-1 STOP (first-class).**

**Mechanism (corpus-independent):** full-stream `collect_checked` under equal weights
visits every root-reachable e-node (cross-check proves marked == reachable); saturation
only adds equalities to reachable classes ⇒ untouched ≈ 0. Ambient's AC fan is
pre-collapsed by `CollectionAcLowering.v::canon_iff_permutation` + the non-linear `Var`
re-bind prune; native-folds are funded + idempotent (`native_refire_is_noop`). No
`SaturationDemandGate.v` / `LabelReachabilityGate.v` is written. Probe:
`dovetail/src/rules.rs::dv0_probe`; ledger `/tmp/p6_probes/findings.md`.

## EP POST-FLIP — RHOCOV-0 (CLOSED 2026-06-17): NON-GOAL (no live application surface)

The RHOCOV idea (when backend=Rho, prune extraction derivations rooted in
Rho-uncoverable rules) is feasible + monotone (coverage is static per-rule:
`lower_language_def` → `lowered`/`rejected`, `lower.rs:571-608`,
`RhoLoweringTotalOrRejects.v`). But it has **no live application surface**, by the
dispatch architecture: `decide_rho_flip` (`flip.rs:56-64`) raises
`RhoFlipBlocker::Coverage` unless coverage is complete, so a language only runs the Rho
backend when it has **zero** rejected rules; the rejected-rule ops (BigInt/BigRat/Float/
cast/collection/ternary/binder/guard) are routed to **Dovetail-direct / native-fold**
(in-engine), where there is no extract-then-reject-on-Rho step. Host-routed langs
(Rholang/GuardedRho) have no extraction-pruning surface at all. ⇒ there is never a
"rejected-rooted extraction root on a Rho-backed extraction path" to prune. **NON-GOAL,
recorded first-class**; the design is banked for a future language that both flips to Rho
AND routes terms through a Dovetail report containing rejected-rooted roots (none today).

## EP POST-FLIP — TR GHOST FIX IMPLEMENTED (2026-06-17): element-category splice gate at the source

Implemented the source-level prevention (3 edits, NO kill site): (1) `WpdaEngine`
trait default `collection_element_src_idx(result, rule, slot) -> Option<u16>`
(`wpda_walker.rs`); (2) codegen override in the generated impl reusing the existing
`emit_collection_element_src_lookup` body (`engine_impl.rs`); (3) the splice gate at the
single `emit_splice_into_collection` call in `apply_pop_body_to_cursor`: refute the
cursor when the spliced top Symbol's `non_terminal_tag` ≠ the rule's element category
(non-kv collections only — kv-maps excluded via `kv_separator_for_collection` since the
lookup keys maps on slot 0 and key/value cats may differ). The faithful post-wrap
Symbol is spliced by a sibling lineage ⇒ no-loss. **GHOSTS GONE** (tr0_ghost_probe:
`{0|1}`/`{0|1|2}`/`{(1)|2}` all 1 term, was 2/3/2; Proc::parse clean). Battery green:
rholang_tests 10/0, wpda_parity_rholang_collections 4/0, edge_case 66/0, prattail lib
3766/0, gen_rholang_{unit 86,rewrite 126,analytical 52}/0, gen_ledtest_{unit 17,
rewrite 20}/0, gen_calculator_unit 169/0, gen_ambient_{unit 10,rewrite 13}/0,
gen_class2hashmapsmoke_unit 5/0, gen_class3multi_unit 6/0. (Post-P6 baselines: op-suites
deleted, counts shifted — rholang_tests 126→10, edge 227→66, prattail 3980→3766.)
ONE prop failure CONFIRMED PRE-EXISTING (A/B): `gen_rholang_prop::proc_display_parse_roundtrip`
— `arb_proc` emitted `str({a} <= {a})`, Proc::parse Err "1:5 found Fixed({)" IDENTICALLY with
the gate on AND off (the error is at the OPENING `{`, upstream of the splice gate) ⇒ a
pre-existing generator/grammar mismatch (str-cast arg can't be a collection), NOT this fix.
Separate ticket. Env toggle removed (plain gate); fix committed `36353578` + regression test
`010cccc6` (collection_ghost_regression 5/5).

**FV DONE @ (this commit), zero-admission:** `CollectionForkEvidence.v` Section
`ElementCategorySoundness` — `into_term_{some,none}_iff_*` (filter_map keep/drop), 
`faithful_finalizes_in_full` (correct parse preserved), `wrong_cat_element_dropped` +
`wrong_cat_strictly_shrinks` (the ghost = a strict sub-multiset), `gate_admits_all_faithful`
(no valid element refused), `refuted_realizes_strict_submultiset` (the gate refuses ONLY
ghosts — no language derivation lost). All 6 `Closed under the global context`; the count-based
`ElementCoverage` provably cannot see this category defect (right count, wrong category), so the
two sections are complementary. `make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-prattail-wpda`
success, 0 warnings.

## EP POST-FLIP — TR GHOST ROOT CAUSE FOUND (2026-06-17, empirically validated): cross-cat element spliced PRE-WRAP

Genesis trace (worktree, parse-time instrumentation, agent a7291864) pinned the TRUE
root cause — correcting BOTH prior hypotheses (kill-site AND per-cursor-arena). The
faithful `{0|1}` and ghost `{0}` come from the SAME SPPF root (#46), realized by ONE
`realize_root_to_terms_with_weights` call. Root #46 has THREE PPar packings (rule 0x2)
whose CollectionId second item is a DIFFERENT-category Symbol:
`[Proc,Proc]`(faithful), `[Proc,UInt32]`, `[Proc,BigRat]`(ghosts). The PPar finalize
action `HashBag::<Proc>::from_iter(drained.filter_map(into_term::<Proc>()))` SILENTLY
DROPS the non-Proc element ⇒ `{0}`. **Upstream genesis:** the collection-element splice
(`emit_splice_into_collection`, called at `wpda_walker.rs:18627` in
`apply_pop_body_to_cursor`) records the element's RAW source-category inner Symbol
(UInt32/BigRat — `1` parses as Int/UInt32/BigInt/BigRat cross-cat) when a competing
lineage pops the element's `CategoryEntry` frame BEFORE the cross-cat WRAP action fires.
So a wrong-category element enters the arena → a polluting `rule=0x2` packing is interned.
WHY GATES MISS IT: ROOT-F G1-G4 govern the fork not element identity; F-2 checks
Term-ness not category (UInt32 DOES realize to a Term, then dropped by into_term);
sep-count sees items=2/seps=1 (consistent); min_terminal_span=0 for collections.

**SOURCE-LEVEL PREVENTION (empirically validated, agent's env-flag experiment — ghosts
gone, suites byte-identical):** gate the splice at `wpda_walker.rs:18627` — refute the
cursor when the spliced top Symbol's `non_terminal_tag` ≠ the rule's ELEMENT category.
The element category comes from a NEW codegen-emitted `WpdaEngine` trait method
`collection_element_src_idx(result_src_idx, rule_idx, slot)` (mirrors
`kv_separator_for_collection`/`is_class3_collection_per_slot`), value =
`lookup_element_src_idx` (`collection.rs:272`). MUST use the true element_src (NOT
`pred_sym.category_src_idx` — that BREAKS List: result cat 8 ≠ element cat 0). Route-
independent (the only discriminator separating the valid nt=0 splice from the invalid
nt=2/3/5 on the SAME edge kind — edge-kind exclusion leaves the List ghost). No-loss:
the post-wrap Proc Symbol is always spliced by a sibling lineage, so the faithful parse
survives; prevented cursor is out-of-language (`into_term::<element_cat>()` = ∅). FV:
extend `CollectionForkEvidence.v::gated_run_iff_loop_lang` with an element-category-
soundness lemma. NEXT: implement (trait default + codegen override + walker gate) →
full battery (rholang 126/0, edge, calc/ledtest op List/Bag/Map, prattail gauntlet) →
FV → commit.

## EP POST-FLIP — TR FIX REDIRECTED (2026-06-17, USER DIRECTIVE): root-cause + PREVENT at source, NO kill site

The round-2 investigation proposed a downstream kill at `packing_satisfies_min_terminal_span`.
**Env-gated instrumentation of that function FALSIFIED the hypothesis:** for `{0|1}` NO
single-item `CollectionId` ever reaches it — only the faithful `[(1,2),(3,4)]` appears.
So the ghost is NOT a distinct under-populated packing caught at that gate. **Observed
genesis:** the ghost is PER-ACCEPTING-CURSOR — `resolve_at_end_of_input`
(`wpda_walker.rs:5726-5740`) yields one root per accepting cursor; `{0|1}` produces ≥2
accepting cursors (one realizes `{0|1}`, one `{0}`); `Proc::parse` only takes
`roots.first()` so its cleanliness is INCIDENTAL. The collection-finalize Symbol is
zero-width `[eof,eof]`, children `[CollectionId]` only. The `kv_phase=0` fork
(`collection.rs:400-559`, G1-G4) does NOT fire a close after a prefix (G1 requires
`token==close`), so the ghost's separator-consume takes a route that **BYPASSES G2**
(`ConsumeCollectionSep`) — advancing past `| 1` without splicing `sym1` into that
lineage's arena (the #313 splice-divergence; the reverted `ac88faeb` sep-count couldn't
catch it). **USER DIRECTIVE (2026-06-17): do NOT add a kill site — find the production
root cause and correct it so the ghost cursor is NEVER produced.** Genesis trace (worktree,
parse-time instrumentation) in flight to pin the bypass route + the most-upstream sound
prevention. FV-first (EvidenceComplete: the prevented cursor is token-unsound / out of the
collection-continuation language, per `CollectionForkEvidence.v::gated_run_iff_loop_lang`).

## EP POST-FLIP — TR-0 (2026-06-17): the `all_alts()` sub-multiset ghost REPRODUCES (fix in progress)

Probe `languages/examples/tr0_ghost_probe.rs` (output `/tmp/p6_probes/tr0_ghost.txt`)
confirms post-`316c34e1`: `parse_Proc_via_wpda_all*("{0 | 1}")` returns `{0 | 1}` AND
the spurious `{0}` (same LexWeight); `{0|1|2}` → `{0|1}`,`{0|2}` ghosts; `{(1)|2}` →
`{1}` ghost. `Proc::parse` is clean (one term) every time. The ghost keeps a PREFIX of
the bag and drops a suffix element — the prefix-sub-multiset-surviving-EOI pattern
(`38dcd485`: "token-soundness violation = legal definite kill"). A dedicated read-only
mechanism investigation (divergence Proc::parse-vs-all_alts, ghost genesis, the
most-upstream sound definite-kill site, blast radius) is in flight; fix is FV-first
(EvidenceComplete: killed = token-unsound = not a valid parse). The `{(1)|2}` 867k-step
spin input parses cleanly here (pos=eof) — the ghost, not a hang, is the live residual.

## EP — Phase 2L (lazy token frontier): IMPLEMENTED + ACCEPTED (experiment 69, 2026-06-18)

**Final verdict: IMPLEMENTED + ACCEPTED.** A prior coarse probe (below) was recorded
as a STOP; the rigorous pgmcp experiment 69 (Welch t, pre-registered, n=60/arm)
**REFUTED that STOP** and accepted lazy lexing. The implementation ships:
`runtime_types.rs::expand_lex_node` (per-node expander extracted from the eager
`lex_dag_core` worklist), `wpda_runtime.rs::LazyLatticeTokenSource`
(`Vec<OnceLock<LexDagNode>>` memoization + a `RefCell` on-demand worklist, computed
when the parser first reads a position), and `automata/codegen.rs::lex_dag_lazy`
(emits a boxed `NodeExpander`). Proven equivalent to eager by `lazy_lex_equivalence.rs`
(7/7 lazy ≡ eager); zero regression (prattail lib 3766, gen_calculator_unit 169,
gen_rholang_unit 86, collection_ghost_regression 5).

### Experiment 69 result (the binding verdict)

Primary metric `lex_build_ns`, decided on the **conservative typical-success workload**
(calculator full-parse, not the most-favorable early-failure case, to pre-empt
cherry-picking):

| class | eager → lazy | Δ | test |
|---|---|---|---|
| calculator full-parse (all 8 inputs) | — | **−4.3…−5.0%** | t=−13.09, p=5.5e-21, d=2.39 → ACCEPT |
| early-failure `}}}` / `* 1 +` | 37.5µs → 10.2µs | **−72.7…−79.3%** | + 97% fewer nodes (37→1) |
| rholang early-failure | — | **−9…−71.7%** | + 90% fewer nodes |
| rholang full-to-EOI (CAVEAT) | 7.97ms → 8.05ms | **+1.0%** | OnceLock overhead when all tokens consumed |

Space (`lex_nodes_materialized`, deterministic): **0% saved on full-parse** (correct —
every token is needed), **90–97% saved on early-failure** (unreached positions never
lexed). Non-parametric robustness on the primary: Mann-Whitney p=6.2e-14, Cliff's
δ=−0.79 ("large"). Net: lazy is a real win concentrated on early-failure/malformed
inputs and small full parses; neutral-to-+1% only on large rholang full-to-EOI parses.

### Why the prior STOP was wrong (superseded, retained for the record)

The original coarse probe (`languages/examples/lex_cost_probe.rs`, since deleted,
2000 reps/input) measured eager-lex vs full parse **only on inputs that parse to
EOI**:

| input | lex_ns | parse_ns | lex% |
|---|---|---|---|
| `1 + 2 * 3` | 3,062 | 2,353,406 | 0.1% |
| `int(3) == 3` | 5,260 | 2,845,199 | 0.2% |
| `float(float(10,64),64)` | 8,733 | 4,124,289 | 0.2% |
| `int(...) ^ int(2) ? y ~ int(...) : int(...)` | 25,675 | 12,892,885 | 0.2% |

It concluded "lex is 0.16% of parse, lazy buys nothing." **The error: it measured
only the full-parse case** — where lazy's benefit is genuinely small (~−4.5% of a tiny
fraction) — and **never measured early-failure/malformed inputs**, exactly where lazy
avoids materializing the unreached token tail (−72…−79% time, 90–97% fewer nodes).
The lesson (logged against [feedback_prove_root_before_claiming]): a measure-first
STOP is only as sound as the input classes it measures; the canonical workload set
must include the early-exit path, not just the happy path.

## EP — Phase 6 (residual dedup/factoring, measure-first) + Phase S (subsumption): STOP (2026-06-18)

Measure-first verdict, grounded in the committed CD-series (the residual-dedup
measurement surface is exactly CD02/CD05/CD06/CD07):
- **CD02 disjoint-FIRST dispatch** (`decision_tree.rs:842-886`, `all_disjoint`): the
  parser dispatches on pairwise-disjoint FIRST sets — it never *constructs* the
  ambiguity that residual dedup would collapse, so dispatch is already deterministic
  (one rule per leading literal). There is no residual PARSE-work to save by dedup.
- **CD05 prefix CSE** (`detect_shared_nonterminal_prefixes:1059`) + **CD06 suffix
  factoring** (`measure_shared_nonterminal_suffixes:1195`): both measured (CD06 I17:
  calc d2=0.19, rholang d2=0.42, Ambient d2=0.57) and both reached **diagnostic-only /
  STOP** — the depth-2 buckets are leading-literal-disjoint under CD02, so factoring is
  code-size-only (zero parse-work savings) and not worth the fresh-nonterminal grammar
  churn (`CD06_SuffixFactor.v` proves the transform sound for any future non-disjoint
  grammar). Phase 6 = the union of these; its verdict is CD06's, generalized: **no
  residual dedup/factoring saves parse work on the production grammars ⇒ STOP.**
- **Phase S subsumption** = the dead-rule mechanism (`decision_tree.rs:364` `dead_rules`,
  consumed by the CD07 dead-rule lint): a rule whose language is subsumed by another is
  *dead* and already detected/reported. There is no separate subsumption-dedup lever
  beyond dead-rule reporting ⇒ **negative result recorded.**
Disposition: Phase 6 + Phase S STOP, first-class, consistent with the CD06 verdict; the
measurement infrastructure (CD05/CD06 + the I17 diagnostic + dead-rule lint) is the
shipped artifact. No further dedup/factoring is wired.

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
- 2026-06-11 P1 I-commit design v1 red-teamed (Round 5, 2 critics) → REDESIGN; **§P1 AMENDED
  (user-approved): parking v2 program** (shadow → new Rocq model → v2 design → re-red-team →
  implement). SHADOW half SHIPPED: PRATTAIL_EP_P1 mode + chokepoint would-share measurement;
  idx 4 would_share_total=3500 == the D dup figure (full-key cross-check PASSES; wrap splits
  nothing on calculator); off-mode inert (control verified); battery green.
- 2026-06-11 v2 M-commit @ a0fa001d: `CrossCatLhsParking.v` — 10 theorems, all `Closed under
  the global context` (T2 member-tail revive soundness; T3 worker-broadcast fence ×2 axes;
  T6/T7 EOI orphan re-drive REQUIRED; T8 wrap refines/cross-host-never-shares). The
  non-vacuous model R5-8 demanded. v2 design round opened (Plan agent + re-red-team next).
- 2026-06-11 v2 design → Round 6 red-team (2 critics, NOT CONVERGED → v3): R6-1 FATAL (the
  16/key parking cap vs 3,311 on one key — the parked-frames substrate cannot hold the class)
  + R6-2..R6-8 corrections; SOUND spine retained. Full record in 03-red-team-ledger.md.
- 2026-06-12 **v3.1 I-COMMIT @ 06e8da4d** (the implementation per 06 v3.1; Step-0 @ 29899972;
  model amendment @ f51ecb74). **FLIP EXPERIMENT (corrected attribution): idx 4 waste
  149,645 → 11,962 = 92% drop (gate ≤59,858 DEMOLISHED); spawns 3,504 → 207;
  consumed_in_place=187; overflow=0; 1.47s → 132ms (11×); outputs identical. ★ idx 6
  (right-censored > 580 s OFF) COMPLETES: 2.67 s ON, consumed=6,949 — THE depth-independence
  acceptance evidence.** Two-state battery: OFF fully at baseline; ON identical EXCEPT ONE
  test — `led_chain_num_to_pred` ("1 + 2 == 3 and 4 == 4" → no result; counters:
  park_overflow_fallbacks=8, inflight_orphan_members=43 — hypothesis: worker-merge starves
  the lineage accounting on MULTI-TOKEN source sub-parses, the in-flight window LedTest's
  `1 + 2` operand opens). **OPEN ITEM (no default flip until fixed + the §5 test set lands):
  dedicated probe investigation → fix → multi-body seed + orphan probe + mid-park budget +
  CollectionMarker fidelity tests → fork-path completeness branch → L-commit Welch.**
  On stays opt-in; default battery byte-identical.
- 2026-06-12 **led_chain TRUE-ROOT fix @ 296c2217** (deep-dive per the corrected methodology
  — flip experiments retired as discovery): parked members strand when the key's WORKER DIES
  mid-parse + EOI re-drive churn; fix = mid-parse dead-worker release (per-key edge tracking,
  post-merge frontier scan, take_inflight_members, Proceed re-injection) + ep_p1_eoi_release.
  Calc structurally unaffected (dead_released=0 corpus-wide).
- 2026-06-12 consolidation + fork-path + §5 gates @ 5a4b3c80 (bookkeeping into
  cursor_gss_push_with_kind; fork-path On decision; R7-10 budget-parity test byte-identical
  k∈{1,4,16,64}; truncation/orphan parity ×3 byte-identical).
- 2026-06-12 **budget-divergence TRUE-ROOT fix @ 9cc1f38c**: the "frontier of 266" was the
  ORPHAN_REVIVAL_FRONTIER_BUDGET gate (InFlight-parked member count at the EOI fixpoint),
  never the live frontier (the lattice path runs Unbounded). An identical accepting config
  was live at EVERY round in BOTH modes; the revival loop re-parked its own re-injections
  (On at ~2× Off's amplification) until the gate aborted an available parse. Fix: skip the
  recovery when a live accept exists (live_frontier_has_accepting_config) — NOT a prune (the
  gate only ever errored; resolved-body alternates drain first). Contract pinned: +7
  zero-admission theorems (accept_skipped_orphan_revival*). NOTE: the guard is
  mode-symmetric and ALSO removed the spurious-revival churn from OFF — re-baselining idx 6:
  the >580 s debug right-censoring was real AT THE PRE-GUARD BASELINE; post-guard release
  OFF ≈ 270 ms/parse.
- 2026-06-12 scan gated on outstanding parks @ 420156b7 (the Welch bare-tower regression
  +1.9%/+3.0% → NEUTRAL; the release exists only to free parked members).
- 2026-06-12 ★ **THE L-COMMIT GATE: Welch panel ACCEPT** (release, N=30/arm, CPU-pinned,
  two-tailed Welch):

  | idx | input class | ctrl ms | treat ms | Δ | p | verdict |
  |---|---|---|---|---|---|---|
  | 0 | d1+cmp | 11.65 | 11.15 | −4.3% | 7e-11 | WIN |
  | 1 | d1+arith | 11.31 | 10.80 | −4.5% | 6e-10 | WIN |
  | 2 | d1 | 10.68 | 10.12 | −5.3% | 3e-12 | WIN |
  | 3 | d3 bare | 60.17 | 59.78 | −0.6% | 0.19 | NEUTRAL |
  | 4 | **d3+cmp** | 6.50 | **3.43** | **−47.3%** | **1e-45** | **WIN** |
  | 5 | d5 bare | 127.35 | 127.40 | 0.0% | 0.94 | NEUTRAL |
  | 7 | 2×d1+cmp | 23.41 | 22.40 | −4.3% | 6e-11 | WIN |
  | 8 | d1 float cmp | 11.99 | 11.49 | −4.2% | 3e-10 | WIN |

  **idx 6 (d5+cmp) release pair: OFF ≈ 270 ms/parse, ON ≈ 7.6 ms/parse — 35×.** Depth
  scaling d3+cmp → d5+cmp: OFF ×41, ON ×2.2 — the depth-independence contract
  (CastLookaheadGateBound + the parking model) realized. Chain neutrality: structural (the
  CrossCatLhs sets are empty on cast-free inputs — the drain/scan paths never run) +
  prattail-lib 3980/0 both cfgs + the bare-tower NEUTRAL rows. **DEFAULT FLIPPED to On**
  (PRATTAIL_EP_P1=off = the kill switch; EP_P1_DEADWORKER_DISABLE = the release's A/B arm).
- 2026-06-12 **the v3 DECIDING MEASUREMENT** (measure-first; EpP1Mode::Measure + the R6-7
  route discriminant making real-cache registration sound + R6-6/B1 first-resolver tail map):
  **idx 4 arrival-phase split = workers 4 / in-flight 24 / RESOLVED 3,476 (99.2%) /
  tail_divergent 0** (totals = 3,504 = the D-commit spawn count exactly; corpus rows: idx0
  2/1/7, idx3 1/3/20, idx5 1/5/208, idx7 4/2/14 — all tail_divergent 0). **R6-1 DISSOLVED:
  v3 = SYNCHRONOUS RESOLVED-BODY CONSUMPTION** (99.2% of arrivals consume the interned body
  in place, zero materialization) **+ bounded in-flight parking** (24 total across ~4 keys ≤
  16/key; overflow→Proceed fallback sound). tail_divergent=0 also confirms the member tails
  agree on this corpus (the v3 member-tail recompute stays per the model's general-case
  fence). =measure neutrality: parses byte-identical, timing unchanged (idx4 1.469s vs
  1.468s baseline).

## P3 — Stage A (pre\*-saturation liveness): DEMOTED → inventory + diagnostic-only

> Plan §P3 (round-2 M-3 demotion). Three deliverables: (1) the Step-(-1) transition inventory +
> entry gate, (2) the recorded STOP (expected), (3) the diagnostic-only shadow measurement
> `prestar_shadow_incremental_over_parikh`. **NO** enforcement, **NO** allow-list build-out, **NO**
> `PreStarLiveness.v` unless the gate unexpectedly passes (it does not). Full doc:
> `07-p3-transition-inventory.md`. Working findings: `/tmp/p3_step/findings.md`.

| Deliverable | Outcome |
|---|---|
| 1. Step-(-1) transition inventory | ✅ `07-p3-transition-inventory.md` — every `WpdaState` (18 intrinsic + 2 terminal, `wpda_runtime.rs:303`), `SymbolKind` frame (5 beyond the model's 3, :53), and `WpdaStepAction` (22, `wpda_walker.rs:508`) tagged {in-model / restricts-only (proof sketch) / must-add} against the `(category, rule_label, position)` skeleton (`build_wpds`, `wpds.rs:425`). |
| Entry gate (`K = 3`) | ❌ **FAIL.** must-add = **17** distinct classes (conservative floor 11). `17 > 3` ⇒ ≈ 5.7×K; floor ≈ 3.7×K. The plan's up-front prediction (FAIL ~5×, ≥15 must-add) is **CONFIRMED**. |
| 2. Recorded STOP | ✅ Inventory is the recorded negative. No model commit, no enforcement, no allow-list. |
| 3. `prestar_shadow_incremental_over_parikh` | ⏹ **honesty STOP** (plan §P3 deliverable-3 final clause + §9 risk 1). The runtime per-cursor liveness query is NOT reuse of the existing analysis surface: every prestar consumer (`check_safety` `verify.rs:60`, `accepts_initial_config` `cegar.rs:447`) queries the SINGLE-symbol start config `symbol_weight(initial_symbol)`; the cursor query needs (a) a runtime→model stack abstraction map, (b) a multi-symbol P-automaton word-acceptance routine (none exists; all helpers are single-symbol), (c) the `stack_fully_modeled` per-cursor guard. The plan FORBIDS building new saturation machinery. The shadow plumbing is therefore NOT added; the predicted/derived incremental **0% < 3%** stands by the same mechanism as the P2 zero (the only obligation-bearing classes live in the must-add `InfixLoop`/`InfixContinuation` configs). |

**The gate-fail (§6) and the deliverable-3 honesty STOP (§7) are the SAME finding by two
independent routes:** the skeleton is too coarse for the runtime configurations, so neither the
offline model nor the runtime probe is admissible without the ≥15 must-add extensions.

**Battery:** P3 ships NO `=shadow` runtime mode (deliverable 3 stops before wiring), so there is no
behavioral surface to validate — the change is doc-only (`07-p3-transition-inventory.md`) + this
ledger entry. Verification is the unchanged-tree confirmation: SENTINEL `gen_ledtest_op` 220/0,
prattail-lib 3989/0 both cfgs, `edge_case_tests` 229/0 (no shadow mode to be inert against — the
inertness is structural: zero code change to the walker/codegen).

### P3 stage log

- 2026-06-12 P3 executed (inventory + entry gate + honesty determination). Source recon: `build_wpds`
  models `(cat, rule_label, position)` with Replace/Push/Pop, single control loc; Sep/Map/Zip/Optional
  loops summarized to one traversal (`wpds.rs:617`); Pratt LHS elided (`skipped_pratt_lhs`, :535);
  `CrossCatLhs`/`Reentry` wrap injection is a live runtime `EdgeKind` (`wpda_walker.rs:7042/7145`).
  Gate FAILS 17 > 3 (floor 11 > 3). Deliverable-3 prestar reuse refuted (multi-symbol word acceptance
  + abstraction map + `stack_fully_modeled` all new). STOP recorded. No Rust/Rocq change.

## P4 — Stages C+E (evidence-weighted ORDERING + innovation/ESS reporting): ESS KEEP, DEMOTION STOP

> Plan §P4. ORDER-ONLY by construction. Model `ForwardOrderOnly.v` @ 8106ec26 (pre-landed M-commit;
> 6 thms incl. T5 `demotion_preserves_accepted_set` + T6 `ess_report_no_prune` — the separate
> `InnovationDemotionOrderOnly.v` the plan §10 lists is SUBSUMED by the T1-T6 consolidation, no new
> model needed). This is the I-commit + L-commit. Working findings: `/tmp/p4_step/findings.md`.

### Deliverables (I-commit, this commit)

| Deliverable | Status |
|---|---|
| ESS reporting (always-on report, computed LAZILY at budget events + EOI) | ✅ `WpdaWalker::frontier_ess_x1000` (Kish ESS = (Σw)²/Σw² over `exp(-primary)` likelihood mass; `rigail` `Semiring::ess_primary_cost` + `LexicographicWeight` override = `primary.value()`); recorded at the 3 budget-sentinel sites (`maybe_prune_frontier` overflow branch + cohort-overflow + orphan-revival BudgetExceeded) and at EOI (`resolve_at_end_of_input`, walker-stats-gated); threaded through the sentinel (`ess_x1000` token) → `WpdaResolveResult::AmbiguityBudget` → `WpdaParseError::AmbiguityBudget` → `ParseError::AmbiguityBudget` hint. Hot path pays NOTHING (computed only at the event). |
| Innovation demotion (kill switch `PRATTAIL_EP_P4_DEMOTE=off\|on`, default OFF) | ✅ `EpP4Demote` mode; per-cursor `BranchCursor::consumed_since_last_check` flag (set after `apply_action_to_cursor` iff `pos` strictly advanced — recovery INSERT holds pos fixed per I8, so a recovery-stall is correctly zero-innovation); carried through the Tomita arc round-trip (mirrors `ep_shadow_refuted`); demotion = STABLE-PARTITION the post-Tomita-drain `drained` order innovating-first WITHIN one `step_fanout` pass. |
| Counters `zero_innovation_demotions` + `demoted_member_unstepped_at_exit` (TRIPWIRE) | ✅ walker_stats.rs; tripwire wired at the runaway-guard early-return AND the normal drain exit. |
| Verification: battery IDENTICAL both states + tripwire == 0 | ✅ (see below) |
| Welch experiment (recovery_cohort_bench + cast_tower_bench) | ✅ (see below) |

### Verification (the accept criteria)

**Battery PASS/FAIL byte-identical both demote states** (order-only): SENTINEL `gen_ledtest_op` 220/0,
`gen_calculator_op` 1330/0, `gen_rholang_op` 530/1 (pre-existing `castbigrat`), `edge_case_tests`
229/0, `rholang_tests` 126/0, `gen_ambient_{analytical,rewrite,prop}` 52/0+13/0+17/0, `prattail
--lib` 3989/0 (default OFF, default ON, AND `--features walker-stats` OFF — all three), `macros`
367/0. `ForwardOrderOnly.v` recompiles clean; the 4 P4 theorems all `Closed under the global context`.

**TRIPWIRE clean:** `demoted_member_unstepped_at_exit == 0` across 14 walker reports on the
recovery-heavy + cast + eval-ambiguous corpus (demote ON + walker-stats); `zero_innovation_demotions`
fired up to 472 ⇒ the within-step invariant (T4/T5) holds, never a deferral across passes.

**ESS report works:** `frontier_ess_x1000_last` observed = 1000 (ESS=1.0, single winner) / 4000 / 10000
(10-way = the cast ambiguity) / 13000; budget-overflow Display surfaces "frontier ESS≈5.000 of 5" +
structured `frontier_ess_x1000=5000` (end-to-end sentinel → result → error → hint confirmed).

### Welch experiments (governor=performance, `taskset -c 0-7`)

| Panel | Result |
|---|---|
| `recovery_cohort_bench` (N=20/arm, interleaved) | off=10.0ms on=10.0ms (sd=0) → **NEUTRAL** (uninformative: 10ms granularity, calc recovery inputs don't trigger the cast equal-weight ambiguity that engages the demotion) |
| `cast_tower_bench` (N=30 light + N=8 heavy incl idx4) | **ALL NEUTRAL** (deltas ±1%, all p>0.05). PARSE-ONLY ⇒ demotion-neutral (the demotion does NOT change parse WORK: `map_put` probe `apply_action_calls=1422`/`step_fanout_calls=70` IDENTICAL OFF vs ON) |
| ★ `rholang_tests` `native_ops::map::map_put` (parse+EVAL) | OFF 0.5s → ON **156.86s (313×)**. The demotion perturbs the 10-way-ambiguous cast WINNER (`CastBigInt` OFF → `CastUInt32` ON; AST flip proven), and UInt32-keyed map eval is pathological. `native_ops` module OFF 2.66s → ON 159.44s. The parse-only benches cannot see this (they don't eval). |

### Verdict (plan §P4 accept criteria; L-decision input — parent decides)

**ESS: KEEP** (always-on, battery-identical, zero hot-path cost, proven diagnostic value).
**DEMOTION: RECOMMEND REVERT (recorded STOP)** per the brief's own fallback. NO panel improves (the
parse-only Welch panels are NEUTRAL — the demotion buys no parse-time win because a complete parse
steps every cursor regardless of order and this walker has no beam/cutoff), AND the eval-inclusive
evidence (map_put 313×) shows the demotion is HARMFUL: it perturbs the ambiguous winner because the
walker's equal-weight tiebreak is order-sensitive (merge `LexicographicWeight::plus` receiver-on-
equality + EOI lex-min), which `ForwardOrderOnly.v` correctly abstracts away by keying ALL surviving
fields into the cursor key — the model is sound; the architecture has no order-neutral reorder
freedom at the continuation-drain surface. Per the brief, the demotion code STAYS (OFF default, kill
switch `PRATTAIL_EP_P4_DEMOTE=on`) — NOT self-reverted; the default (OFF) is byte-identical to baseline.

### P4 stage log

- 2026-06-12 P4 I-commit: ESS reporting (lazy, budget+EOI) + innovation demotion (OFF default) +
  tripwire. Battery byte-identical both states; tripwire 0 everywhere; ESS surfacing confirmed
  end-to-end; `ForwardOrderOnly.v` 4 thms `Closed under the global context`.
- 2026-06-12 P4 L-commit (Welch + verdict): cast_tower_bench + recovery_cohort_bench parse-only
  panels NEUTRAL; the DECISIVE eval-inclusive datum (rholang map_put 313× under ON, via a perturbed
  cast winner — AST `CastBigInt`→`CastUInt32` proven by flip) ⇒ **KEEP ESS, RECOMMEND REVERT
  DEMOTION** (recorded STOP; demotion left OFF-by-default, parent decides the L-flip).

## P5 — Stage D (regular residual over-approximation gate): ENTRY-GATE = STOP

> Plan §P5 entry gate (measure-first; no `RegularResidualGate.v`, no codegen, no enforcement unless
> the gate passes). `residual_dead_steps` reduces (P2-real-refuted = 0 [P2 STOPped, no enforcement];
> P2-shadow-refuted = 0 [ledger §P2]; P3-shadow-refuted = 0 [§P3 honesty STOP]) to: apply_action
> steps on cursors that DIE at the EOI `!is_accepting_config` filter, as % of `apply_action_calls`.
> GATE ≥ 15% ⇒ implement Stage D; < 15% ⇒ STOP. Working findings: `/tmp/p5_gate/findings.md`.

### Measurement (measurement-only; uncommitted; default ep_p1=On world)

Per-cursor `BranchCursor::p5_steps_{own,lineage}` (NON-cfg u32, the `ep_shadow_refuted` precedent;
incremented at `apply_action_to_cursor` entry; carried through the `FrontierArc` Tomita round-trip).
**own** (LOWER bound) = own apply_action calls since birth; fork→children born at 0; merge-absorb→
survivor SUMS the loser (ConfigKey merge + Tomita `register_arc_with_aggregation`); a strict
partition of `apply_action_calls`. **lineage** (UPPER bound) = ancestry path length; fork→all
children inherit; merge→MAX. Accounted in `p5_account_eoi_frontier` (a read-only pass over
`self.branch_cursors`, called BEFORE the stats dump — the resolution snapshot path runs post-dump and
the deterministic fast-path bypasses it; classifies each cursor via the SAME `is_accepting_config`).

| Corpus | parses | apply_action | EOI examined (dead) | dead[own/lin] | residual_dead% | pre_eoi_lost% |
|---|---:|---:|---:|---|---:|---:|
| cast_probe 0/3/4/5/7/8 | 6 | 7,363 | 6 (0) | 0/0 | 0.0000 | 98.87 |
| `rholang_tests` (126/0) | 2,137 | 204,004 | 4,891 (1,706) | 0/0 | 0.0000 | 76.75 |
| `gen_ledtest_op` SENTINEL (220/0) | 708 | 45,373 | 1,224 (0) | 0/0 | 0.0000 | 49.85 |
| `gen_rholang_op` (530/1 castbigrat) | 8,242 | 388,399 | 20,444 (2,254) | 0/0 | 0.0000 | 37.92 |
| **CORPUS-AGGREGATE** | **11,093** | **645,139** | **26,565 (3,960)** | **0/0** | **0.0000** | — |

### P5 entry-gate verdict (2026-06-12): **STOP — recorded, first-class (H13/CD06/P2/P3 precedent)**

**`residual_dead_steps` = [0.0000% .. 0.0000%]** of `apply_action_calls` corpus-wide (own LOWER ..
lineage UPPER bracket); 0% ≪ 15% on BOTH bounds ⇒ unambiguous STOP. **Do NOT implement Stage D /
`RegularResidualGate.v`.** The plan's predicted ALL(*) lesson ("the cheap gates already took the
volume") is CONFIRMED.

**Mechanism (deep-dived, not an artifact):** 3,960 cursors DO die at EOI across the corpus — the
population is non-empty — but EVERY one carries `p5_steps_own = p5_steps_lineage = 0`. They are
re-seeded TERMINAL states (post-`AmbiguityFanout`-resolution singletons, post-drop write-backs,
freshly-materialized cohort members) that reach EOI WITHOUT re-entering `apply_action_to_cursor`. The
real parse work (37.9–98.9% of apply_action, the `pre_eoi_lost` bank) is consumed MID-PARSE by the
existing dispatch resolution + P1 parking, which collapse the fan well before EOI. A regular-over-
approximation residual DFA (Stage D's mechanism) would prune ~ZERO apply_action work: the EOI-death
cursors are already step-free terminals, and the upstream fan is already collapsed by cheaper
mechanisms. The own-partition identity `dead_own + accepted_own + pre_eoi_lost = apply_action_calls`
holds exactly per parse (e.g. idx0: 0 + 15 + 192 = 207). A naive "all pre_eoi_lost is dead" upper
bound (37.9–98.9%) is UNSOUND — it would attribute progress-work (ancestry that produced the
surviving accepting singleton) and mid-parse Drops (not an EOI-death; outside Stage D's target) to
the EOI-death class; the faithful §P5 quantity is 0.

**Verification (measurement-only, no behavior change):** SENTINEL `gen_ledtest_op` 220/0; prattail-lib
**3989/0 BOTH cfgs** (default + `--features walker-stats`); `edge_case_tests` 229/0 (FRESH-built
default cfg — the non-cfg counter + fork/merge SUM/MAX paths are inert); `gen_rholang_op` 530/1
(pre-existing `castbigrat`); both cfg builds green. Full record: `/tmp/p5_gate/findings.md`.

### P5 stage log

- 2026-06-12 P5 entry-gate measured: per-cursor own/lineage step counters (bracket) + EOI-frontier
  accounting pass. Deep-dived the initial all-zero surprise to mechanism (stats-dump-before-flush
  probe artifact → deterministic fast-path → frontier collapses to 1 accepting cursor at EOI →
  EOI-deaths are step-free re-seeded terminals). Corpus-aggregate residual_dead_steps =
  [0.0000%..0.0000%] ≪ 15% ⇒ **STOP** (expected; the ALL(*) lesson). No model, no codegen, no
  enforcement. Battery at baseline (SENTINEL 220/0; prattail-lib 3989/0 both cfgs; edge 229/0).
