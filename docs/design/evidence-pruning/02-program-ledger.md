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
11,962 attributed steps), ProcX root-fan, post-ROOT-A rhocalc send/receive, + the adversarial
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
rhocalc_tests, ledtest_op, rhocalc_op); refuted_then_accepted = 0 (the tripwire never fired).
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
