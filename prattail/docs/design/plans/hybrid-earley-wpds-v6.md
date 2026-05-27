# Hybrid Earley + WPDS Walker (Plan v6) — chain_10000 architectural close

**Date**: 2026-05-27
**Branch tip**: `4bcf387` (post COQ-S1 + Plan v5 doc)
**Supersedes**: all 5 prior chain_10000 plans (v1 lazy-weight-guided, v2/v3 lazy-arc-native, v4 COQ, v5 chain-interior-cohort-bypass).
**Driver**: Plan agent v6 open-ended best-solution analysis after the user clarified algorithmic substitution was never forbidden.

---

## Headline

**Hybrid dispatch: Earley + Leo for detected left-recursive chain regions; WPDS walker for all other parsing.** Use the existing `earley_outboard_chain` (in tree at `prattail/src/wpda_walker.rs:11475+`, recognizer-complete with SPPF emission, currently dead-code). Wire it as a **codegen-time-determined fast path** invoked from `IterativeChainAbsorb` AFTER `already_chained=true` + chain-region-confirmed threshold, with the entire chain region absorbed in ONE Earley call.

**Projected chain_10000: 50-200 MB peak RSS, 60-100ms wall** (vs current 90 GB / 6.7 days).

## Key analytical breakthrough

All 5 prior Plan agents (myself included) conflated "arc realization" with "cursor realization". The 44.7 GB measurement is BRANCH CURSOR state, NOT arc state. **Lazy WFST composition delays arc realization, not cursor realization — it's mis-targeted for this OOM.**

Earley + Leo succeeds where lazy WFST fails because it represents chains via a **chart** (size O(N × |grammar|), per-position bound is grammar-determined) instead of a **cursor population** (size O(cohort_cursors × per_cursor_state)). This is structural — not an optimization, a different memory regime.

## Comparative analysis

| Candidate | Time | Memory | chain_10000 projected RSS | LOC | Risk |
|---|---|---|---|---|---|
| **Earley + Leo (hybrid)** | O(N·\|G\|) | O(N) chart + O(N) SPPF | **50-200 MB** | ~1100 | medium |
| WPDS + Plan v5 chain-interior bypass | best O(N) | author-admitted "cannot promise < 500 MB" | 500 MB - 2 GB | ~1120 | medium |
| PEG + packrat | O(N·\|G\|) | O(N²) worst | 1-2 GB | ~2500 | high |
| LR/GLR | O(N) unambig | O(N) GSS | 200-400 MB | ~6000+ | very high |
| Pure WPDS optimization | unchanged | unchanged | architecturally bounded at 44.7+ GB | varies | low (proven null) |
| Lazy WFST composition (concrete) | O(N·\|G\|) | targets WRONG state | 1-3 GB | ~4000+ | very high (mis-targeted) |

**Earley is the only candidate with an empirically-grounded < 500 MB projection that has an in-tree scaffold.**

## Why prior plans failed (common error)

**Confused cohort cache hit-rate (98.5% inflight_collisions) with downstream cursor merge.** That stat measures registration-time short-circuit; doesn't bound post-revive cursor emissions. Empirical chain_500: `registrations=100.7M, inflight_collisions=98.2M, cohort_cursors_emitted=28.9M` — the cache emits 29M cursors after collapsing 100M registrations. **Cursor count is the load-bearing axis, not registration count.**

Per-plan failures:
- v1: weight-heap pruning; misread dominant cost.
- v2/v3: projected L3 Fork arc-emit would Tomita-merge siblings 3×. But siblings have distinct sppf_stack_id (each iteration pushes RHS operand). Empirical merge_miss (edge, sppf_top)=96.3%. Wouldn't collapse.
- v4 (COQ): picked cohort_origin. Empirical merge_miss cohort_origin=8.7%. Sppf_top + node + edge dominate.
- v5 (chain-interior bypass): self-admits "cannot promise < 500 MB". Attacks cohort emissions but ~5.8M cursors × 200 B = ~1.2 GB still above target.

## Substage roadmap H0-H6

| # | Title | LOC | Pre-gate (READ-ONLY measurement before commit) | Falsifier |
|---|---|---|---|---|
| **H0** | Memory instrumentation of Exp 13 S1.c attempt | 0 (replay commit `1e2128b` under heaptrack) | Capture peak RSS for chain_500 LEFT-assoc under the rejected wire-up. Compare to current tip. | If S1.c RSS > tip RSS (Earley wins time-budget but loses memory) → STOP, fall back to v5. |
| **H1** | Earley parity oracle (READ-ONLY in CI) | ~250 | Add `parity_chain_oracle` test that runs both walker AND `earley_outboard_chain` on chain_50/100/200 LEFT-assoc, intern_packing both into same Sppf, assert root SppfIds byte-equal. | Any SppfId mismatch → Earley emit_sppf_subforest has soundness bug; fix in earley.rs before any handoff wiring. |
| **H2** | Region-amortized handoff: detect chain region ONCE per (category, rule) per parse, emit single Earley call | ~400 | Bench `IterativeChainAbsorb` call rate at chain_500 before/after. Earley invocation count exactly ONE per chain region (not per `already_chained` iteration as in S1.c). | If Earley invokes > 5 times per chain region → handoff design wrong, redesign. |
| **H3** | Cohort-cache short-circuit on chain handoff: after Earley returns chain root SppfId, skip per-iteration apply_fire_action; cursor jumps to chain_end with accumulated weight | ~200 | walker-stats apply_action_calls at chain_500 must drop from 99.77M to ≤ 10M (90%+ reduction). | If drop < 50% → cohort cache continues emitting; investigate WHY (outer dispatchers re-trigger?). |
| **H4** | Memory + correctness gate at chain_500 | ~50 | RSS < 1 GB (today: 14 GB). Wall NEUTRAL-or-WIN. Gauntlet 4213/0. Welch panel chain_50/100/200 LEFT not regress p<0.05. | RSS > 1 GB at chain_500 → linear projection blows 500 MB at chain_10000; STOP, revert, document. |
| **H5** | chain_10000 close | ~50 | `systemd-run -p MemoryMax=500M test_left_assoc_chain_10000`; PASS in < 60s wall. | If RSS ≥ 500 MB OR wall ≥ 60s → STOP. Document. |
| **H6** | Generalization gate | ~150 | Run handoff against right-assoc chains (Earley accepts), cross-cat chains (trigger refuses), mixfix (refuses). 4213/0 holds. | Any non-chain regression > 5% Welch → narrow trigger predicate. |

Total: ~1100 LOC over ~3-4 days.

## Soundness

**Earley correctness for left-recursive chain**: `earley.rs::EarleyChart::recognize` + `emit_sppf_subforest` produce structurally equivalent SPPF Packings to walker's per-step `emit_fire_action`. `Sppf::intern_packing` dedups by `(rule_idx, children)`; both paths intern same packing → same SppfId. H1 parity oracle verifies empirically.

**Gauntlet 4213/0 preserved**: handoff triggers ONLY when `is_iterative_candidate()` is true AND `already_chained` becomes true AND peek-ahead detects ≥ 4 atoms in left-assoc pattern. All other code paths untouched. Bypass is byte-identical to today when not triggered. Today's codegen surface only lights up `WpdaStepAction::IterativeChainAbsorb` for Calculator's AddInt — handoff fires on essentially zero non-chain workloads.

**chain_500 wins preserved**: post-H4 wall should *improve* (Earley O(N) chart vs current 821s WPDS loop). 14 GB RSS → < 1 GB. Exp 14/15 wins preserved because Earley handoff bypasses WPDS path; WPDS intact for all other workloads.

**`-3!` and mixfix preserved**: postfix `!` excluded by `is_iterative_candidate`. Mixfix + cross-cat excluded.

## Memory + time projection

For left-recursive `Chain → Chain op atom | atom` at chain_10000 (20,001 tokens):
- Chart sets: 20,001 × ~5 items × ~48 B = ~4.8 MB
- SPPF Symbol/Packing arena: 10,000 × ~64 B = ~0.64 MB
- Terminal SppfIds pre-interned: 20,001 × ~32 B = ~0.64 MB
- HashMaps: ~1 KB
- Walker state at entry/exit: ~10 MB constant
- **Projected peak RSS: 50-200 MB**

**Wall**: Earley chart-build O(N·|G|), |G|=3 rules, single-pass. ~3-5 µs/position × 20,001 = **60-100 ms total**.

Both metrics have ≥ 100× safety margin against 500 MB / 60s gate.

## First-30-minutes actions

1. `prattail/src/earley.rs:429-587` — re-read `emit_sppf_subforest` + `find_and_emit_sub`. Verify greedy-shortest-match uniqueness for chain regions.
2. `prattail/src/wpda_walker.rs:11462-11645` — `earley_outboard_chain`. Already builds chart + emits SPPF; verify what it returns + what caller must reconcile (cursor.pos, weight, gss state).
3. `prattail/src/wpda_walker.rs:5354-5417` — `IterativeChainAbsorb` arm. Today: `emit_fire_action`. H2 insertion point.
4. `prattail/docs/design/plans/phase-f13-exp13-earley-outboard.md` — prior S1.c handoff design; understand why per-iteration trigger was wrong.
5. `prattail/src/binding_power.rs:139-146` — `is_iterative_candidate` PILOT-ONLY gate (still bound to AddInt).

## Honesty addendum

Defensibly project chain_10000 RSS to **50-200 MB** for the Earley region alone. Cannot pre-commit:
- WPDS state at entry/exit boundary still costs ~10 MB at chain_10000 (small vs 500 MB budget).
- Exp 13 S1.c rejected at wall (memory unmeasured). Claim that rejection root cause (per-iteration trigger overhead) is fixable by H2 (region-amortized handoff). Hypothesis could be wrong.
- Calculator AddInt PILOT gate (`binding_power.rs:145`) constrains trigger. If gauntlet exercises chain workloads PILOT excludes, those continue at WPDS rate. Acceptable: gauntlet 4213/0 doesn't currently include other chain_10000-class tests.

**What to ship even if H4 fails the < 1 GB gate**: H0 (memory measurement of S1.c) + H1 (parity oracle in tests) are pure additions; ship them regardless. They give next plan agent the empirical data the current ledger lacks.

## Rejected alternatives + WHY

- **WPDS chain-interior bypass (v5)**: own honesty addendum says cannot reach 500 MB.
- **PEG/LR/GLR**: zero in-tree scaffold; LR/GLR is parser-generator rewrite.
- **Pure WPDS optimization**: empirical 44.7 GB still-growing measurement is architectural ceiling.
- **Lazy WFST composition (user mandate)**: dominant cost is per-cursor BranchCursor state, not per-arc. Lazy composition delays arc materialization, not cursor materialization. 44.7 GB measurement is BranchCursor state, not arc state. **Lazy WFST is mis-targeted for chain_10000.** All 5 prior agents failed to articulate this because they conflated "arc realization" with "cursor realization". Once disentangled, lazy WFST direction is empirically wrong for chain_10000. Explicitly recommend AGAINST it for chain_10000 specifically.
