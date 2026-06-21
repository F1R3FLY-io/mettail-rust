# Phase F.13 Exp 13 — Earley + Leo outboard chain-region delegation

**Status**: Plan agent design captured 2026-05-26. **S1.a in progress**; S1.b–S1.e are queued multi-session work.

**Tip**: `c6eb865` (Exp 10 S0-bis + Exp 13 S0 instrumentation shipped).

**Goal**: close the `test_left_assoc_chain_10000` 24 GB OOM ceiling by delegating long chain regions to an outboard Earley + Leo recognizer (`prattail/src/earley.rs`, currently 347 LoC, coded but unwired). At handoff threshold ~1000 iterations, ~90% of a chain_10000 parse runs under Earley → dispatch cache never sees those positions → projected ~9× cache-growth reduction (3.7 GB/min → ~0.4 GB/min → fits in 16 GB comfortably).

**Why Earley vs Exp 9 Approach P (REJECTED)**: Approach P deferred cursor EMISSION; cache state still grew because `pending_members` + `cohort_shell` populated at every cohort pause. Earley bypasses the walker's `IterativeChainAbsorb` arm entirely → the dispatch cache never gets populated for chain positions → genuinely different mechanism than Approach P.

**Plan agent caveats (RECOMMEND GO)**:
1. Bottleneck might not be cache growth alone. If GSS edges grow per-iteration (unlikely given Exp 6's shared Return frame invariant), Earley won't help. Verify in S1.c with `walker-stats` GSS edge counters.
2. The 347 LoC in `earley.rs` are untested at scale. Hidden bugs likely (the `complete` filter at line 159 is suspicious; `scan` is a no-op).
3. Multi-packing aggregation may diverge — gate to deterministic mode / single-cursor.
4. Eligibility: `lex_fork_path.is_empty() AND cohort_origin.is_none()` — chain_10000 with single-char `+` tokens satisfies trivially; mixed-lex chains fall through to walker.

---

## Substage decomposition (~680 LOC total across 5 substages)

### S1.a — `EarleyChart::emit_sppf_subforest` (~150 LOC, additive)

Extend `EarleyChart` with:
```rust
pub fn emit_sppf_subforest<W: SemiringRef>(
    &self,
    sppf: &mut Sppf<W>,
    root_category: &str,
    root_nt_tag: u32,
    rule_label_to_idx: &HashMap<String, u32>,
    op_terminal_id: SppfId,
    atom_terminals: &[SppfId],
    op_weight: &W,
) -> Option<SppfId>;
```

Walks chart top-down from the recognizing item at `sets[input_len]`, intern Symbols + Packings + links. Pure read-only over the chart; SPPF mutations confined to the method.

Also: fix the latent bugs found while reading earley.rs (the `complete` filter at line 159, `scan` no-op).

Acceptance: 10+ unit tests pass + gauntlet 4124/0.

### S1.b — `WpdaWalker::earley_outboard_chain` method (~250 LOC, additive, unreachable)

Adds method that:
1. Detects end-of-chain-region via linear forward peek
2. Builds `EarleyChart` for `tokens[cursor.pos..end]`
3. Adds 2-3 grammar rules from `(category_src_idx, rule_index_in_category)`
4. Drives `predict + scan + complete + leo_reduce` over the slice
5. Calls `chart.emit_sppf_subforest(...)` to lift back
6. Returns `Option<(SppfId, W, usize)>` = (root, weight, end_pos)

Standalone test on 100-token slice; not yet integrated.

Acceptance: standalone test passes + gauntlet 4124/0.

### S1.c — Trigger detection in `IterativeChainAbsorb` arm (~80 LOC)

Add `BranchCursor::current_chain_streak: u32` (resets on non-IterativeChainAbsorb arms; increments on `already_chained = true`).

At `wpda_walker.rs:5200` after the streak increments:
```rust
if cursor.current_chain_streak >= EARLEY_HANDOFF_THRESHOLD
    && cursor.lex_fork_path.is_empty()
    && cursor.cohort_origin.is_none()
    && (self.deterministic || self.branch_cursors.len() == 1)
    && self.peek_chain_continues(cursor, tokens, &symbol)
{
    if let Some((root, w, end)) =
        self.earley_outboard_chain(cursor, tokens, &symbol, weight.clone(), new_state.clone())
    {
        return self.reconcile_after_earley(cursor, root, w, end, new_state);
    }
}
```

**Falsifier**: any chain_50-1000 LOSS p<0.05 → REVERT. chain_10000 RSS < 16 GB at 8 min wall = ACCEPT.

### S1.d — SPPF lift-back + reconciliation cleanup (~120 LOC)

The reconciliation per design §5:
1. `chain_weight = sppf.symbol_weight_sum(chain_root_sid)`
2. `cursor.pos = end_of_chain_region`
3. Pop the per-iteration `emit_fire_action`'s last pushed Symbol via `arena.intern_pop(cursor.sppf_stack_id)`
4. Push `chain_root_sid` via `arena.intern_push`
5. `self.multiply_cursor_weight(cursor, &chain_weight)`
6. Drop to `WpdaState::InfixLoop { cur_bp: outer_bp }`
7. Reset `cursor.current_chain_streak = 0`

Debug assertion: `sppf.symbol_weight_sum(chain_root_sid) == earley_weight` catches accounting drift.

**Falsifier**: same as S1.c. If S1.d passes, re-enable `test_left_assoc_chain_10000` (`#[ignore]` removed at `trampoline_tests.rs:195`).

### S1.e — Chain-region end detection robustness + threshold tuning (~80 LOC)

- Collect `chain_region_iterations` for chain_10000 with `EARLEY_HANDOFF_THRESHOLD ∈ {100, 500, 1000, 5000}`
- Pick smallest non-regressing threshold
- Harden end-of-chain detection for edge cases (trailing EOF, mid-token errors, lex alternatives present at boundary)

**Falsifier**: preserves S1.c-d acceptance AND monotonic chain_10000 improvement vs S1.d's threshold.

---

## Correctness gates (L1-L6 + Earley-specific)

| Gate | Mechanism | Earley handoff satisfies |
|------|-----------|--------------------------|
| L1 GSS purity | Single Return RuleAt frame shared; we don't touch GSS | Preserved |
| L2 cohort lazy | Handoff requires `cohort_origin.is_none()` | Bypassed cleanly |
| L3 ObsInvariant fast-path | ObsDivergent by nature (mutates weight/state/pos/sppf_stack_id) | Compatible |
| L4 Arc-shared cycle defense | `visited_*` untouched | Preserved |
| L5 hybrid merge | Post-Earley ConfigKey matches non-Earley at same end-pos | `merge_equivalent_cursors` works |
| L6 5th+ packing bug | `intern_packing` dedup by (rule_idx, children) | Preserved by API |
| E1 lex provenance | Hard-gated `lex_fork_path.is_empty()` | Pathological cases fall back |
| E2 cohort drain | Hard-gated `cohort_origin.is_none()` | Hard-gated |
| E3 dedup with walker packings | `link_packing_to_symbol` is idempotent | Preserved by API |
| E4 weight aggregation parity | `intern_packing` ⊕-aggregates on dedup hit | Preserved by API |

---

## Risk register

1. **Unwired code = untested**. earley.rs has 6 unit tests, none exercising large inputs or weight aggregation. S1.a bumps coverage; expect 1-3 latent bugs.
2. **Cursor reconciliation novel** — S1.d's debug assertion catches accounting drift.
3. **Multi-packing aggregation divergence** — gate to deterministic / single-cursor.
4. **Cohort revive interaction** — verify streak resets across cohort revive emissions.
5. **Earley file ≠ full grammar** — 3-rule subset; chains interrupted by non-conforming token bail to walker for remainder. Test in S1.d.
6. **EARLEY_HANDOFF_THRESHOLD too low** → false positives. S1.e tunes; default conservative at 1000.
7. **Earley's `complete` arm O(n²)** for LEFT-recursive grammars (our case). Leo doesn't help here. 10K chain → ~50M comparisons → ~1 sec. Acceptable but watch.

---

## Test coverage

Primary target: `test_left_assoc_chain_10000` (line 195, currently `#[ignore]`). RE-ENABLE in S1.d if RSS gate passes.
Welch baseline: `test_right_assoc_chain_{50,100,200,1000}` (lines 131-155). Must stay ACCEPT.
Secondary: `test_right_assoc_chain_10000` (line 166, `#[ignore]`) — requires `is_iterative_candidate` gate broadened (currently PILOT-ONLY `label == "AddInt"`).
Stack-safety regression: `test_deep_parens_*` (lines 96-126).

Gauntlets:
- `cargo test -p prattail` → preserve 4124/0
- `cargo test -p languages --test trampoline_tests` → 15/0/2 (or 15/0/0 if chain_10000 closes)
- `cargo test -p languages --test wpda_parity_calculator` → 16/0

---

## Recommended execution order

1. **S1.a** (chart + lift-back, additive). Catch latent earley.rs bugs early. ~1 session.
2. **S1.b** (method exists, unreachable). Standalone bench on 100-token slice. ~1 session.
3. **Empirical pre-check** before S1.c: confirm chain_region_iterations fires at chain_1000 left-assoc.
4. **S1.c** (trigger wired). Welch sweep N=15. ~1 session.
5. **S1.d** (reconciliation hardened + chain_10000 measurement). The headline. ~2 sessions.
6. **S1.e** (threshold tuning). ~1 session.

**Total: 6-7 sessions, ~680 LoC across 5 commits + 1 ledger update.**
