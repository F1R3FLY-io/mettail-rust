# Sig-B Fix — Cross-Cat Cycle-Defense Key-Symmetry (2026-05-31)

**pgmcp experiment #9** (`cast-family-sig-b-...`). Root cause PINNED by a runtime M1-vs-M4 differential trace
(artifact #4 on #9; logs `/var/tmp/suite-green/sigb-{m1,m4}-*.log`). NOT hypothesized — measured.

## Root cause (evidence-grounded)
M4 widens the cohort CACHE key (`DispatchKey += {wrap_cat,wrap_rule}`, `dispatch_cohort.rs:63`) but leaves the
cross-cat CYCLE-DEFENSE key NARROW: `extract_dispatch_config` (`wpda_walker.rs:2710`) packs
`PackedDispatchConfig(pos:40, cat_src:16, cur_bp:8)` — a full u64, no wrap. The **B14-C5 pure-projection-Fork
cycle gate** (`wpda_walker.rs:6684` `is_pure_projection_fork && parent_in_visited` → `Drop :6697`; per-branch
`:6845` skip) consults this narrow key. Under M4, distinct un-conflated cross-cat dispatches (different
`(wrap_cat,wrap_rule)` ⇒ different `sppf_top` ⇒ different inner derivations) collapse to ONE narrow config and are
dropped as **false "projection cycles"**. Measured: distinct cohort keys 29→75 / 35→112; B14C5 Fork-DROPs 14→394
(28×); the valid `BoolToInt`-path cursor is dropped → `branch_cursors` empties → terminal `Error` (bypasses EOI
revival `:3962`) → "no accepting branch … '(' " at `self.pos=1`. **H1 (revival) + H3 (merge-drop) FALSIFIED** by
measurement (dying cursors are graduated, not paused; all 4000/4000 merge-collapses have identical full keys).

This is **premature disambiguation by the cycle-defense heuristic** — it rejects a sound, genuinely-distinct GLL
descriptor as a cycle. Forbidden per the standing mandate.

## Principled fix — restore key-symmetry (GLL-correct, ambiguity-preserving, WPDA-integrated)
The cross-cat cycle-defense is a GLL-descriptor dedup; a descriptor is a true cycle ONLY if it re-enters the SAME
dispatch. Two cross-cat projections that differ in `(wrap_cat,wrap_rule)` are DISTINCT descriptors, not a cycle.
**Widen the cross-cat cycle-defense key to carry `(wrap_cat,wrap_rule)`** — the SAME axis M4 added to `DispatchKey`
— so the B14-C5 gate rejects only true self-cycles and lets distinct ambiguous dispatches propagate end-to-end
until real evidence (a true wrap-identical re-entry / EOI / the shipped Step-A token-soundness filter) rejects them.
NO weight, NO cap, NO heuristic, NO test-hack. The cast rule is reachable only via its real keyword Fork → sound.

## Memory-safe layout — Welch-DECIDED (the u64 pack exists for chain memory)
`PackedDispatchConfig` is a full u64; adding the wrap needs a layout decision, chosen by the MANDATORY chain
Welch+RSS gate:
- **Option A (preferred — memory-neutral on chains):** SCOPE the widening. Keep the general `visited_dispatch`
  narrow u64 (chains, which are NOT cross-cat, are byte-identical). Add a separate cross-cat-only
  `visited_cross_cat_dispatch: Arc<FxHashSet<u128>>` (pos+cat_src+cur_bp+wrap_cat+wrap_rule, full precision)
  populated + consulted ONLY at the B14-C5 cross-cat gate. Chains never populate it (empty Arc → O(1) clone) →
  zero chain memory cost.
- **Option B (simpler — global widen):** `PackedDispatchConfig` → u128 (pos40+cat_src16+cur_bp8+wrap_cat16+wrap_rule16).
  Fully correct but doubles every `visited_dispatch` entry (8→16 B) → chain RSS risk.
- **Rule:** try B first (simplest); if the chain Welch panel LOSES any arm (p<0.05) or chain_1000/2000 RSS
  regresses >5%, switch to A. Do NOT truncate the wrap into spare u64 bits (a >256-category/rule grammar would
  re-conflate = premature disambiguation).

## Sequencing
This fix sits ON TOP of M4 keying (`rework-m2-m4keying.patch`) + the banked realize-fix (in the main tree).
Together: M4 (16 fixed) + realize-fix (4 of the 9 regressions) + this cycle-defense fix (the other 5 Sig-B) ⇒ the
9 M4-regressions all return green with the 16 fixes kept. The nested cluster (`test_nested_int_int` etc., Proc-entry
`registrations=0`) is a SEPARATE recognition concern — handle after.

## GATE (experiment #9 acceptance)
- 5 Sig-B green: `parse_int_cross_cat_comparison_le`, `simulator_regression_{original_6,cross_cat_dispatch_chaining,cross_cat_with_floats,bool_prefix_tokens}`.
- 16 M4-fixed stay fixed; 4 realize-fixed stay fixed; `parse_int_cross_cat_comparison_{ge,ne}` + `_in_expression` stay green.
- gauntlet `cargo test --release -p prattail --lib`=4220/0; op-suites gen_calculator_op≥1331/gen_rhocalc_op 532.
- C-bis cycle/newton/tarjan/star/scc/self_loop tests 0-fail; soundness probe + `-3!` + `wpda_parity_*` green.
- **MANDATORY interleaved Welch chain panel** `{left,right}_assoc_chain_{50,100,200}`+right_1000, N≥51 (per #9
  protocol), no arm LOSS p<0.05; chain_1000/2000 RSS +5% max. (The cycle-defense touches the visited_dispatch
  cursor machinery → chain perf/memory is the load-bearing regression guard.)
- Ambiguity-preservation: the un-conflated distinct cross-cat derivations must SURVIVE to EOI (verify the Sig-B
  parses produce the expected term, and that genuinely-ambiguous inputs still yield `Ambiguous(...)`).

## Risks
R1 chain RSS regression (Option B) → mitigated by Option A scoping (Welch-decided). R2 the wrap discriminator must
match M4's exact `branch.symbol.{category_src_idx,rule_index_in_category}` so the cycle-defense and the cohort cache
agree. R3 a TRUE projection cycle (genuine infinite re-projection) must STILL be caught — verify the
wrap-identical-re-entry case still drops (a self-cycle has identical wrap) via a targeted test + the existing
projection-cycle regression tests.
