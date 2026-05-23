# Phase F.13 Cohort Ambiguity Preservation — Plan

**Status:** Plan agent design (2026-05-22). Targets `precedence_associativity_stress::postfix_binds_tighter_than_unary` (`-3!`).

**Tip:** `35e591e`.

## 1. Empirical Confirmation

Documented empirical facts (from prior diagnostic prints + earlier Explore comparisons):
- Lex-Fork at pos=0 emits Branch A (Integer "-3", `lex_alt_idx=0`) AND Branch B (Minus "-", `lex_alt_idx=2`).
- Dispatch table maps Int+Fixed("-") → Neg(PrefixOp).
- Cohort sharing OFF: 23 normal forms include `-6`.
- Cohort sharing ON: 9 normal forms, no `-6`.

## 2. Root Cause (refined)

The `ConfigKey` at `wpda_walker.rs:1641` carries `(state, node, pos, edge, depth, cohort_origin, sppf_top)` but NOT `weight.lex_alt_idx`. At `merge_equivalent_cursors:7192`, two sub-cursors with the same configuration but distinct lex-Fork provenance MERGE → lex-min picks the lower `lex_alt_idx` (Branch A) → Branch B dies BEFORE its Neg outer-reduce fires → `intern_packing(Neg, …)` never happens → realize from `Symbol(Int, 0, 3)` only enumerates `Fact` packing.

The `LexicographicWeight::lex_alt_idx` field exists (introduced L1 2026-04-28) and is stamped at lex-Fork emit sites; `times` left-projects it (preserved along the cursor's path). It is treated as "weight tiebreak payload" rather than "parse identity discriminator" — that is the gap.

## 3. Option Ranking

| Option | Sound | Disruption | Effort | Risk | H12 preservation |
|---|---|---|---|---|---|
| **A — lex_alt_idx + src/rule_idx in ConfigKey** | **1** | **1** | **1** | **2** | **1** |
| B — Cohort split on internal ambiguity | 2 | 3 | 3 | 3 | 2 |
| C — Approach P realize-time fanout | 2 | 5 | 5 | 4 | 3 |
| D — Eval-fail backtracking | 5 | 4 | 2 | 5 | 1 |
| E — Multi-packing fallback at intern_packing | 4 | 2 | 1 | 3 | 1 |
| F — Snapshot Vec per sub-cursor (depends on A) | 2 | 3 | 2 | 3 | 2 |
| G — Combination of A + E (+F) | 1 | 1 | 1 | 1 | 1 |

**Recommended: Option A (with Option E as defensive belt-and-suspenders).**

## 4. The Fix (concrete)

### 4.1 Schema extension in `wpda_walker.rs::ConfigKey`

```rust
struct ConfigKey {
    state: WpdaState,
    node: GssNodeId,
    pos: usize,
    incoming_edge: Option<GssEdgeId>,
    collection_depth: usize,
    cohort_origin: Option<DispatchKey>,
    sppf_top: Option<SppfId>,

    // Phase F.13 Stage 2.0 (2026-05-22): GLL/Tomita descriptor
    // completion — lex-Fork provenance. Two cursors at the same
    // (state, node, pos, edge, depth, sppf_top, cohort_origin) but
    // with distinct lex_alt_idx are DISTINCT PARSES under different
    // lex-disambiguation choices and MUST NOT merge.
    lex_alt_idx: u16,
    weight_src_idx: u16,
    weight_rule_idx: u16,
}
```

### 4.2 Populate at merge site (line 7192)

```rust
let key = ConfigKey {
    state: cursor.inner_state.clone(),
    node: cursor.node,
    pos: cursor.pos,
    incoming_edge: cursor.incoming_edge_stack.last().copied(),
    collection_depth: cursor.collection_stack_depth as usize,
    cohort_origin: cursor.cohort_origin.clone(),
    sppf_top: cursor.sppf_stack.last().copied(),
    // Stage 2.0:
    lex_alt_idx: cursor.weight.lex_alt_idx,
    weight_src_idx: cursor.weight.src_idx,
    weight_rule_idx: cursor.weight.rule_idx,
};
```

**Total: ~10 lines of code.** No changes required to `dispatch_cohort.rs`, `cursor_gss_pop_via_edge`, or `revive_cohort_member_with_snapshot`.

## 5. Soundness Proof

**Theorem.** `T_coh(input) ⊇ T_per(input)` for all inputs, where `T` is the multiset of normal forms produced.

**Proof sketch.**
- *Lemma 1*: engine purity → cohort sub-parse output ≡ per-cursor sub-parse output (Symbol-dedup).
- *Lemma 2*: ConfigKey faithfulness → two cursors with distinct lex_alt_idx never merge (after §4.1).
- *Lemma 3*: cohort revival preserves cohort member's `lex_alt_idx` via `times` left-projection (`lex_weight.rs:410-422`).
- *Lemma 4*: worker-internal sub-cursors from lex-Fork retain distinct `lex_alt_idx` → never merge → each fires its own `emit_fire_action` → SPPF accumulates ALL packings.
- *Lemma 5*: per-cursor baseline ⊆ cohort path: every per-cursor realization survives under cohort sharing with §4.1.
- ∴ Theorem. ∎

**H12 preservation**: chain_50/100/200 have NO lex ambiguity → every cursor has `lex_alt_idx=0` → no new cursor multiplicity introduced.

## 6. Staging (6 commits)

| # | Stage | Scope | Verification |
|---|---|---|---|
| 2.0a | Schema extension (no behavior change) | Add fields + Hash/Eq derive coverage | Gauntlet 6160/1 unchanged |
| 2.0b | Populate fields at merge | Read `cursor.weight.{lex_alt_idx,src_idx,rule_idx}` into key | `-3!` PASSES; gauntlet ≥ 6161/0 |
| 2.0c | Welch perf gate | 30× chain_50/100/200 before/after; p > 0.05 | Documented |
| 2.0d (optional) | E defensive opt-out | Multi-packing detection at `link_packing_to_symbol` | Unchanged from 2.0b |
| 2.0e (optional) | Validate `cohort_origin` obsolescence | Empirical check: is cohort_origin still needed? | Gauntlet ≥ 6161/0 |
| 2.0f (optional) | Stage 1.5.3R revert (if 2.0e validates) | Remove `cohort_origin` field + revive tag + graduation logic | Gauntlet ≥ 6161/0 |

## 7. Effort: 1.0–1.5 working days (primary fix + perf gate)

- 2.0a + 2.0b: 4–6 hours.
- 2.0c (perf gate): 4 hours.
- 2.0d (optional defensive): 4–6 hours.
- 2.0e + 2.0f (cleanup): 6 hours.

## 8. Risk Register

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| Over-discrimination via src_idx/rule_idx bloats chain cursor count | Low | Medium (perf) | 2.0c Welch gate; narrow to lex_alt_idx only if needed |
| Realize produces redundant duplicates per Packing | Low | Low | downstream dedup unchanged |
| cohort_origin (Stage 1.5.3R) becomes obsolete | Medium | Low | 2.0e validates |
| Snapshot cap drops snapshots in pathological grammars | Low | Medium | Existing cap; opt-out via 2.0d if needed |
| Non-lex sites with lex_alt_idx=0 default cause spurious collisions | Low | Low | All non-lex cursors share lex_alt_idx=0, merge as before |

## 9. Why This Hasn't Been Done

Prior plans (Stage 1.5.3R `cohort_origin`, Alt#1 `sppf_top`) addressed DIFFERENT collapse modes. None added `lex_alt_idx` — the field was treated as "weight payload" not "parse identity." Option A closes this gap with ~10 LoC.

## 10. Fallback Hierarchy

1. G-synthesis (A + E): 1–2 days.
2. Approach R (4-hour bail-out at multi-packing).
3. Approach P (Stage 1.5.4, 2–3 weeks, plan in `phase-f13-stage-1-5-4-approach-p-realize-time-fanout.md`).
