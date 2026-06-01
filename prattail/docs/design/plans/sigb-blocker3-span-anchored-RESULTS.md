# Sig-B Blocker-3 SPAN-ANCHORED RECONSTRUCTION — IMPLEMENTATION RESULTS (pgmcp experiment #9)

Design: `sigb-blocker3-span-anchored-reconstruction.md` (FIFTH redesign). Base = `6507b9c`
+ `sigb-cast-family-COMPLETE.patch` (Blocker-2). Worktree `/var/tmp/wt-b3-span`. Evidence
artifacts in `/var/tmp/suite-green/b3-span-m70-*.{stderr,log}`.

## Base reproduction (PASS)
- gauntlet `cargo test --release -p mettail-prattail --lib` = **4220/0** (`b3-span-m70-base-gauntlet.log`).
- calc `cargo test --release -p mettail-languages --test calculator` = **210/7** (`b3-span-m70-base-calc.log`):
  the 3 B3 targets (`test_nested_float_float_int`, `test_triple_nested_float`,
  `simulator_regression_bool_prefix_tokens`) + 4 pre-existing eval-ambiguity
  (`test_int_add_overflow_wraps_in_release`, `test_int_pow_31_wraps_in_release`,
  `test_uint32_add_overflow_wraps_in_release`, `test_bool_from_list_elem`).
- Blocker-2 markers present (`wrap_cat`/`take_pending_for_drain_crosswrap`/`crosswrap_drained`/
  `crosswrap_backstop_for_pausing_member`); M5.1 `take_outer_cast_revival` ABSENT (build on B2, not M5.1).

## M7.0 — INERT diagnostic-confirm (commit 231ff8c). VERDICT: SPLIT (Bool PROCEED, Float STOP).

Added (all read-only / gated): `single_hop_coercion` codegen (RETAINED from
`b3-coerce-m60-DELTA.patch`); `b3_disabled`/`b3_span_disabled` gates (unread at M7.0);
`make_probe_cursor`; `sigb_m70_span_diagnostic` (gated `SIGB_CROSSWRAP`) — prints the SPPF
`(lo_pos,hi_pos)` span + the SPAN-ANCHORED pairing scan (`R.span_lo == K_sib.pos`) the M6.0
survey omitted. Wired at `step_fanout`'s `branch_cursors.is_empty()` pre-Error drop site.

MECHANICAL GATE: gauntlet 4220/0; calc 210/7 (== Blocker-2); chain Welch structurally
NEUTRAL (hot path byte-identical, survey gated off; full N≥51 panel deferred to M7.3).

### Bool family — `[C7-1]`, `[C7-2]`, `[C7-3]`, `[C7-6]` REPRODUCED → PROCEED to M7.1.
- `[C7-1]` FIRST-ambiguity: the var-first `int(y != true > x < "qua")` drops to
  `branch_cursors.is_empty()` (survey fires); the passing boollit-first
  `int(false > b < -2080280922)` NEVER drops (survey fires 0×) — the liveness asymmetry.
- `[C7-2]` (overturns M6.0 R1): the full-span Bool body `sym=91 SPPF_span=[2,9] body_cat=7`
  exists, keyed at `pos_at_dispatch=4`. It SPAN-ANCHORS (`R.span_lo=2 == K_sib.pos=2`) to the
  paused outer-cast member. 953 span-anchored pairs / 360 cat-compatible+fire-ok on the target.
- The GENUINE outer member is `K_sib{pos:2, src:7(Bool), wrap:(1,11)=BoolToInt}` (from the
  `REGISTER key={pos:2,src:7,bp:0,wrap:(1,11)}` in `b3-coerce-m60-T1bool.stderr`). `tgt_cat=7`
  (Bool) == `body_cat=7` → DIRECT splice (no coercion); the member's own wrap `(1,11)=BoolToInt`
  fires → Int. EQUIVALENTLY reachable via `K_sib{src:1, wrap:(0,9)}` + `single_hop_coercion(7,1)=
  (1,11)` → COERCE fire Some `output_cat=Int(1)` (also confirmed in the scan).
- `[C7-3]` span-anchored fire + pos-align: every genuine pair fires `Some` with
  `member.pos=2 → R.span_hi=9` (consumes `)` at 9). CONFIRMED.
- `[C7-6]` `min_terminal_span` backstop intact (BoolToInt(1,11)=1, ProcFloat(0,8)=0).
- NOTE: `:2189` (`int(y and b == y < "x")`) already PARSES on Blocker-2 (confirmed without the
  survey gate). Only `:2188` (`int(y != true > x < "qua")`) is the genuine Bool residual within
  `simulator_regression_bool_prefix_tokens` — narrower than the design §0 assumed.

### Float family — `[C7-4](b)` / `[C7-5]` FALSIFIED → STOP (split verdict per design §7 R2).
- `[C7-4](a)` confirmed: NO Resolved entry spans the outer `[2,10]`; cross-cat registers cluster
  at the INNER `float(10,64)` region.
- `[C7-4](b)` FALSIFIED: a FULL-SPPF arena scan (not just the cohort cache) finds NO Float
  Symbol spanning the inner `[2,7]` (`float(10,64)`) NOR any Symbol spanning the outer `[2,10]`.
  The only Float symbols are the ATOMIC literals `[4,5]`(=10) and `[6,7]`(=64). The widest span
  that EVER reduces to a Symbol is `[4,8]` (a spurious Fixed read). **The inner 2-param FloatBin
  fold never produces a Float Symbol at all** — there is no body to span-anchor and no `[C7-5]`
  candidate to construct.
- `[C7-4](c)` confirmed: `single_hop_coercion(Float=6, Proc=0) = (0,8)` = ProcFloat (fires Some
  `output_cat=Proc(0)` over the ATOMIC `[4,5]` Float, but never over an inner-FloatBin result).
- CONCLUSION: the Float gap is DEEPER than the span-anchor (d-i) or the forward `ProcFloat`
  projection-fire (d-ii) — both presuppose the inner Float `[2,7]` Symbol exists. It does not.
  The defect is in the nested 2-param-fold reduce itself (the inner `FloatBin . a:Proc, w:Int |-
  "float" "(" a "," w ")" : Float` never completes its reduce when `a` is itself a `float(...)`).
  This is a distinct residual requiring its own plan (a 2-param-fold nested-reduce investigation),
  NOT addressable by `take_span_anchored_outer_cast`. STOP per `[C7-4]` STOP gate.

## M7.1 — wire §2.4a Bool span-anchored revival + §2.4c coercion. VERDICT: BOOL CLOSED.

Added:
- `DispatchCohortCache::take_span_anchored_outer_cast<E>(&mut self, sppf, engine)` — the
  EOI/pre-Error drain. Scans ALL Resolved bodies `R`; for each paused member `K_sib`
  (InFlight or shorter-span Resolved with non-empty members) tests clause-2 (EquivKey),
  clause-3 (`R.span_lo == K_sib.pos` SPAN ANCHOR), clause-4 (`body_cat==tgt_cat` OR
  `single_hop_coercion(body_cat,tgt_cat)≠∅`, carrying the coercion into the job),
  clause-5 (take-once via the SHARED `crosswrap_drained`). Forward
  `take_pending_for_drain_crosswrap` + §3d backstop stay BYTE-IDENTICAL (each just gained
  `coercion: None` on its job ctor). `CrossWrapSpliceJob` gained an `Option<(u16,u16)>` coercion.
- `WpdaWalker::intern_coercion_over_body` — interposes the depth-1 coercion Symbol over the
  body, REUSING the exact `emit_fire_action` intern shape (intern_packing + intern_symbol at
  the body's span + `fire_action_via_transient` store into `sppf_symbol_terms`); returns the
  wrapped Symbol id (or None on elide → evidence-driven drop). DEDUP'd by `(nt,lo,hi)` (no SPPF growth).
- `WpdaWalker::revive_span_anchored_outer_cast_members` — drains the jobs, interposes the
  coercion when present (else raw body), revives via the existing
  `revive_cohort_member_with_snapshot` (`pos_at_dispatch = K_sib.pos`, `hi_pos = R.span_hi`).
- Two retention sites: `step_fanout`'s `branch_cursors.is_empty()` (pre-Error) and
  `run_to_end_of_input`'s `!progress_made` (EOI, alongside `revive_orphaned_cohort_members_once`).
  Both inject ≥1 cursor → re-enter the fanout loop (`AmbiguityFanout`) instead of Error/clean-exit.
  Gated `!b3_disabled() && !b3_span_disabled()`.

M7.1 GATE (PASS):
- **`:2188` (`int(y != true > x < "qua")`) PARSES** → `int(y != true > x < "qua")` (token-sound display).
- `simulator_regression_bool_prefix_tokens` (both var-first inputs) GREEN.
- 3 M3.1 sentinels GREEN: `simulator_regression_cross_cat_dispatch_chaining`,
  `simulator_regression_cross_cat_with_floats`, `test_nested_int_int`.
- `simulator_regression_cross_cat_with_parens` + `simulator_regression_cross_cat_with_strings`
  + `test_nested_int_float` + all 4 `parse_int_cross_cat_comparison_{ge,ne,lt,le}` GREEN.
- gauntlet 4220/0; **calc 211/6** (was 210/7; +1 Bool target; remaining 6 = 2 Float STOP + 4 eval-ambiguity).
- `B3_DISABLE=1` ⇒ `:2188` ERR (restores Blocker-2). `B3_SPAN_DISABLE=1` ⇒ `:2188` ERR.
- **Splice count on the Bool target = 14 distinct `(K_sib, body)` pairings** (≪ M5.1's 16251,
  a >1000× reduction); the drain fires ONCE (1 retention injection), parse completes in 0.19s (no hang).
- R8 (the genuine BoolToInt member not directly span-anchored) did NOT manifest: the
  SPPF-dedup + `merge_equivalent_cursors` + the span-anchored revival of the available
  pos:2 members (with §2.4c coercion interposition) collectively resolve the genuine derivation.
