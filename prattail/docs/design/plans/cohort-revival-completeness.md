# Cohort-Revival-Completeness Mechanism — Implementation Plan (2026-05-31)

**Repo:** `/home/dylon/Workspace/f1r3fly.io/mettail-rust` (PraTTaIL). **Branch:** `feature/wfst-architecture`,
HEAD `6507b9c` + validated session fixes (`git diff --shortstat` = 18 files / +1498 / −175; snapshot
`/var/tmp/suite-green/current-tree-2026-05-31.patch`). **Delta under test:** `/var/tmp/suite-green/rework-m2-m4keying.patch`
(M4 `DispatchKey += {wrap_cat,wrap_rule}`; `EquivKey`/`PackedDispatchConfig`/merge kept NARROW). **Closes:** the M4
un-conflation shippability gap (16 FIXED stay fixed; 9 REGRESSED return green; the Int-entry cross-cat tail).
Produced by a Plan agent that re-traced both drop signatures under M4 in an isolated worktree (DEBUG `--features
walker-stats` build capturing the decisive `realize_packing_call:5305` "action elided" count). Main tree pristine.

## 0. HARD INVARIANT
NEVER prematurely drop a SOUND derivation. The mechanism MUST make the un-conflated SOUND derivations REACH
realizable accepting roots. Drops happen ONLY by EVIDENCE: token-soundness (Step-A `min_terminal_span` filter,
`wpda_walker.rs:4843-4884` + `WpdaEngine::min_terminal_span:257`/codegen `semantic_actions.rs:116`), a cursor that
cannot reach an accepting branch, or EOI exclusion. NO weight/cost heuristic. `Ambiguous(...)` first-class.
**EquivKey MUST stay narrow** (`dispatch_cohort.rs:121` — the COQ-S1 chain O(N²)→O(N) fix). `PackedDispatchConfig`
stays a full u64 (zero free bits).

## 1. EMPIRICAL GROUND TRUTH (traces supersede prior framing)
- **G1 — Sig-A (`int(-1 <= 0)`, the 9 regressions + bare-var):** `registrations=271`, **`inflight_orphan=0`**,
  **`action elided=0`**, `merge_collapses=2403`; `distinct_dispatch_keys=41 → distinct_equiv_keys=6` (M4 un-conflation
  confirmed). Result "accepting cursors had no extractable terms" (`:4420`). **ROOT:** the SOUND un-conflated cursor
  (e.g. the `BoolToInt` worker carrying the resolved inner Bool Symbol, about to Return-pop and fire its outer cast
  `action_fn` → `intern_packing`+`link_packing_to_symbol`) is **collapsed and dropped at `merge_equivalent_cursors`
  (`:10349-10466`, narrow-EquivKey bucket via `.equiv()` `:10317`, lex-min tiebreak `:10392`, loser discarded
  `:10461`) BEFORE it reduces its outer packing.** The merge's design assumption (`:10366`/`:10490` "structural
  ambiguity now lives in the SPPF arena") holds only for ALREADY-REDUCED cursors; it FAILS for an un-conflated cohort
  cursor dropped mid-flight → the accepting Symbol's `packings_of` is ∅ (or only token-unsound siblings the Step-A
  filter then correctly drops) → realize empty. This is candidate **(b)** sharpened: the sound packing is **never
  interned** (cursor dies pre-reduce). NOT (c) cycle-defense (`would_drop=0`), NOT (d) Step-A over-rejection
  (`action elided=0`; the sound packing is ABSENT, not rejected).
- **G2a — SUITE `test_nested_int_int` = `calc_normal_form("int(int(5,32),32)")` → `parse_term` → Proc-entry:**
  **`registrations_total=0`**, 2 forks, dies "no accepting branch". The cohort NEVER engages. This is the **R2
  codegen recognition gap** (`cohort-correctness-rework.md` M3) — the Proc-entry 2-arg cast slot-0 (`a:Proc` via
  `ProcInt` projection) does not admit a nested cast. **OUT OF SCOPE for this mechanism (codegen R2).**
- **G2b — Int-entry deep cross-cat (`int(-220439700 > 1827376848 == c != -0.5)`, a REGRESSION):** `registrations=8629`,
  `orphan=178 (<256)`, `merge_collapses=136944`, `action elided=0`, "no accepting branch". SAME merge-drop root as
  Sig-A PLUS a revival-incompleteness tail (the orphan=0 members of the same test fail via the Sig-A route).
- **G2c — `Int::parse("int(int(5,32),32)")` (orphan=258 > 256):** spurious-gate evaluates `parse_already_succeeds`
  = FALSE (zero accepting cursors) → **correctly does NOT skip**. The gate is NOT misfiring; the threshold is fine.
  Revival exhausts `MAX_REVIVAL_ROUNDS=4` + re-collides.
- **G3 — why revival is incomplete:** (1) bound `MAX_REVIVAL_ROUNDS=4` (`:955`/`:8620`); (2) **re-collision** —
  `drain_orphaned_inflight_members` removes the whole entry so the FIRST re-driven orphan is `WorkerInserted`, but
  N>1 same-key orphans re-collide → re-paused, so even UNBOUNDED rounds can't converge by re-drive alone ⇒ **pure
  fixpoint-revive (candidate b) is insufficient**.
- **G4 — M4 surface confirmed:** `DispatchKey` widens `{wrap_cat,wrap_rule}` (`:13185`); `equiv()` strips them
  (`:121`) ⇒ EquivKey narrow; `EdgeKind::CrossCatProjection` carries them (`gss.rs:404`). For `int(…)` the 4 unary
  casts (`FloatToInt`/`BoolToInt`/`StrToInt`/`IntId`) are distinct wrap_rules AND distinct EquivKeys → the Sig-A drop
  is the sound cohort cursor colliding with a GRADUATED/concrete cursor at the same outer ConfigKey (graduation
  clears `cohort_origin` `:14022-14030`), not the 4 casts against each other.

## 2. Candidate-mechanism evaluation
| Mechanism | Sig-A (merge-drop) | revival tail | G2a regs=0 | HARD INV | EquivKey narrow | chain/O(N²) risk | Verdict |
|---|---|---|---|---|---|---|---|
| **(a) Continuation-install, cross-cat-gated** | **YES** (re-supplies the sound packing at EOI independent of cursor fate) | **YES** (no re-drive) | NO (pre-cohort) | YES (Step-A sole drop) | YES | LOW iff capture gated `!pos_in_absorbed_chain_interval` | **RECOMMENDED** |
| (b) Gated-fixpoint-revive | NO (orphan=0) | PARTIAL (G3.2 re-collision) | NO | risk | YES | HIGH (re-drive = ternary O(N²)) | rejected |
| (c) SPPF-merge-aggregation | PARTIAL (no packing exists at merge — cursor dropped pre-reduce) | NO | NO | — | YES | MED (merge is chain-hot) | insufficient |
| (d) widen cycle-defense | n/a (`would_drop=0`) | no | no | — | — | u64 layout change | not indicated |

**(a) beats (c):** `action elided=0` + sound packing ABSENT proves it is never interned (cursor dies pre-reduce);
(c) can only aggregate packings that EXIST. (a) reconstructs the packing from the continuation
(`outer_rule_idx`+`other_children`+resolved `symbol_id`) and interns/links it at EOI, independent of cursor fate —
the ONLY candidate closing Sig-A by construction. It also closes the revival tail (capture at PAUSE, install at EOI,
no re-drive). **(b)/(c) NOT needed.** G2a (regs=0) → existing R2-codegen. Spurious-gate UNCHANGED (G2c).

## 3. Verified machinery (line-exact, current tree under M4)
- **Keys:** `DispatchKey{pos,source_src_idx,inner_cur_bp,wrap_cat,wrap_rule}` (`:63`); `EquivKey` via `.equiv():121`;
  `PackedDispatchConfig(u64)` cycle-defense (`:2672`, full u64).
- **Lifecycle:** register `:13219` → `InflightCollision`→`pause_cohort_member dispatch_cohort.rs:818` (cap 16); worker
  Return-pop → `resolve:13991`→`take_pending_for_drain:584`; end-of-step drain `step_fanout:9403`→
  `revive_cohort_member_with_snapshot:13410`.
- **EOI:** `run_to_end_of_input:3932`→`revive_orphaned_cohort_members_once:8611` (spurious gate `:8690`; bound `:955`);
  `resolve_at_end_of_input:4000` (collect `:4286`; ≥2-arm `:4376`; Sig-A landing `:4420`).
- **Realize:** `realize_root_to_terms_with_weights:4555`; `realize_node_leave:4711` Symbol arm `:4804-4902` (Step-A
  filter `:4843-4884`); `realize_packing_call:5305` action-elision drop.
- **SPPF:** `intern_symbol:535` (dedup `(nt,lo,hi)`); `intern_packing:560` (dedup `(rule_idx,children)`);
  `link_packing_to_symbol:672` (idempotent); `packings_of:727` (realize iterates ALL).
- **DEAD asset:** `cohort_continuation.rs` (`CohortContinuation{outer_rule_idx,outer_cat_src_idx,outer_lo_pos,
  other_children:Vec<SppfId>,substitution_slot,weight_at_dispatch}`, ~32 B; `MAX_DEFERRED_PER_KEY=64`); field
  `deferred_continuations` on InFlight (`dispatch_cohort.rs:239`) + Resolved (`:274`); preserved through `resolve()`
  (`:504/:514`); stats-read only. NEVER constructed/installed. Eligible when worker dispatch is at the last child
  slot (`substitution_slot=arity-1`, `other_children`=prefix) — true for unary casts + chains.
- **Chain gate:** `pos_in_absorbed_chain_interval:12547` (true only strictly inside a `chain_absorbed_intervals`
  entry; map empty off chain hot path — the byte-identical shipped R4 chain-suppression predicate `:13197`).

## 4. Standing GATE (every milestone)
gauntlet `cargo test --release -p mettail-prattail --lib`=**4220/0**; op-suites `gen_calculator_op≥1331/0`,
`gen_rhocalc_op 532/0`; `-3!` + `wpda_parity_*` /0; soundness probe `pass2c_token_soundness_probe`; over-gen canaries
`simulator_regression_{nested_casts,bool_prefix_tokens}` + `probe!` set (`bool(0)`,`int(int(3))`,…) GREEN; **16-FIXED
stay fixed**; **9-REGRESSION return green**; **MANDATORY interleaved Welch chain panel `{left,right}_assoc_chain_{50,100,200}`
+ right_1000, N≥15, no arm LOSS p<0.05, + chain_1000/2000 RSS +5% max** (the prior Approach-P rejection was a chain
LOSS — gating MUST be Welch-proven inert; baselines `welch-interleaved.txt`/`welch-baseline-rss.txt`);
`test_deep_ternary_{100,500,1000}`+`test_ternary_chain_10000` ≤5% wall (gate unchanged → guard).
**Housekeeping:** isolated worktree (`git worktree add --detach /var/tmp/wt-M<n> 6507b9c && cd && git apply
current-tree-2026-05-31.patch && git apply rework-m2-m4keying.patch && cp <mainrepo>/Cargo.lock .`); remove when done;
main tree NEVER modified (verify `git -C <mainrepo> diff --shortstat` stays 18/+1498/−175).

## 5. Milestones
### M0 — Census + merge-drop proof counter (measure-only)
`#[cfg(feature="walker-stats")]` in `merge_equivalent_cursors:10354`: `merge_dropped_distinct_cohort_workers` (loser
has `cohort_origin.is_some()` AND its `sppf_stack` top is NOT a reduced outer Symbol; bucket winner/loser equiv
match-vs-differ). In `revive_orphaned_cohort_members_once:8720`: `revival_recollisions_total` + final `revival_rounds`.
PREDICT: Sig-A `int(-1<=0)` `merge_dropped…≥1`; G2b `merge_dropped…≥1 AND revival_recollisions≥1, rounds==4`. GATE:
standing (measure-only). Revert: delete counters. **(Confirms G1/G3 before building the install.)**

### M1 — Continuation CAPTURE at pause (cross-cat-gated, inert; no install)
In the `InflightCollision` cross-cat arm (`wpda_walker.rs:13227-13246`, before `pause_cohort_member`): when
**P-eligible** (worker `CrossCatDelegate` dispatch at the last child slot) AND **`!self.pos_in_absorbed_chain_interval(pos_after)`**
(chain guard), build a `CohortContinuation`: `outer_rule_idx/outer_cat_src_idx` = `branch.symbol.{rule_index_in_category,
category_src_idx}` (already in scope `:13185`); `other_children` = the outer rule's pre-dispatch children from the
pausing member's `sppf_stack` (slice the `return_frame.sppf_stack_id` via `sppf_stack_arena`); `substitution_slot`;
`outer_lo_pos`; `weight_at_dispatch` = `parent.weight.times_ref(&branch.weight)` (`:13218`). Push into the InFlight
entry's `deferred_continuations` (cap 64; overflow falls through to today's pause = safe degrade). Generalize asset
eligibility from chain-only `slot=arity-1` to any faithfully-capturable slot (unary cast: arity-1 slot-0; 2-arg
IntBin: `slot=0`,`other_children=[width_symbol]`); fall back to today's per-cursor revive when not faithfully
capturable. GATE: standing + **Welch panel + RSS** (PREDICT NEUTRAL; hard sub-gate: `deferred_continuations_len==0`
on every chain rep). M0 counter unchanged (no install → suite identical to plain M4). Risk: gate predicate wrong →
capture leaks onto chains → Welch LOSS; mitigation = the byte-identical R4 predicate + the `==0`-on-chains sub-gate.
Revert: additive → plain M4.

### M2 — Continuation INSTALL at EOI (closes Sig-A + revival tail)
NEW `install_cohort_continuations(&mut self)` at TOP of `resolve_at_end_of_input:4000` (before collect `:4286`):
drain `deferred_continuations` from every entry (add `drain_all_deferred_continuations` to `DispatchCohortCache`
mirroring `:681`). For each with a RESOLVED worker `symbol_id` at its key (Resolved entry, or a resolved sibling's
symbol): substitute `symbol_id` into `other_children` at `substitution_slot` → `children`; `pk =
sppf.intern_packing((outer_cat_src_idx<<16)|outer_rule_idx, children, weight_at_dispatch)`; `sym =
sppf.intern_symbol(outer_cat_nt_tag, outer_lo_pos, hi_pos)` (dedups to the SAME `(nt,lo,hi)` the accepting cursor's
outer Symbol uses); `sppf.link_packing_to_symbol(sym, pk)`. → the sound outer packing joins `packings_of(sym)` →
`realize_node_leave` iterates it; Step-A filter (`:4843`) is the SOLE post-hoc drop. Make
`revive_orphaned_cohort_members_once:8611` DEFER to the continuation path for P-eligible cross-cat sites (do NOT
re-drive orphans that have a captured continuation; only re-drive non-P-eligible mixfix) → bounded revive + spurious
gate become INERT for cross-cat (closing G2b/G2c WITHOUT raising the bound or touching the gate; deep-ternary path
unchanged). `Ambiguous` preserved (≥2 sound continuations → ≥2 packings → realize enumerates all; NO weight). GATE:
standing + M0 shows 16-FIXED stay + 9-REGRESSION return + accepting Symbol `packings_of` non-empty for `int(-1<=0)`
+ **re-Welch panel + RSS** (PREDICT NEUTRAL; install is once-at-EOI, O(#continuations) grammar-bounded off-chain,
ZERO on chains). Risks: over-gen (mitigated by Step-A + canaries — a red canary ⇒ wrong `other_children`/slot capture,
not a filter bug); wrong `(nt,lo,hi)` (derive lo/hi from the resolve-entry fields; debug-assert `intern_symbol` dedup
hit — VI-2); chain RSS (M1 gate ⇒ zero continuations on chains + explicit RSS sub-gate). Revert: → M1.

### M3 — Spurious-blowup gate subsumption statement (gate UNCHANGED)
NO threshold/condition change (G2c proved it correct). Doc-comment at `:8627-8689` that cross-cat P-eligible orphans
now install (M2) and never reach the gate → its sole role is deep-mixfix spurious-tail suppression. Optional
`#[cfg(walker-stats)]` assert: any orphan reaching the gate has `cohort_origin` but NO captured continuation. GATE:
standing + deep_ternary wall ≤5%. **Verdict: gate RETAINED unchanged, merely bypassed for cross-cat by M2.**

### M4 — Bare-var reconciliation (only if residual after M2)
If `bare_variable_infers_as_proc` still red: `infer_term_type` (`language.rs:3460/3826`) — top-level bare var reports
`Proc` when `Ambiguous⊇Proc` AND Proc is declared primary, WITHOUT dropping Name from the term set. GATE: standing +
`bare_variable_infers_as_proc`, `comm::single_channel`.

### M5 — Hand G2a (regs=0 nested recognition) to the existing R2-codegen milestone
NOT this mechanism. `test_nested_int_int`/`_float_float_int`/`test_triple_nested_float` fail via Proc-entry
`registrations_total=0` = `cohort-correctness-rework.md` M3 (admit cross-cat first-arg in 2-arg-cast slot-0,
`prefix.rs:1076-1197`+`CrossCatLhs:1433-1453`, span-filter-bounded, NO weight). Sequence: land M0–M3 HERE first
(closes Sig-A + Int-entry cross-cat), THEN R2-codegen; the nested cluster closes via the COMBINATION (R2 recognizes;
this mechanism carries the un-conflated sound derivation to the root — the install path is recursion-agnostic).

## 6. Open verification items (resolve during impl, not blocking)
- **VI-1.** M0 counter confirms the Sig-A loser is dropped against a graduated/concrete cursor (`cohort_origin` cleared
  `:14022-14030`), pinning the ConfigKey collision class.
- **VI-2 (critical).** `install_cohort_continuations` reaches the SAME `(nt,lo,hi)` Symbol the accepting cursor points
  at (debug-assert `intern_symbol` dedup hit); if the worker died before its own reduce, install must `intern_symbol`
  fresh AND an accepting cursor must REACH it (`is_cursor_accepting_terminal:11358` requires a single-Symbol sppf_stack
  top). **If no accepting cursor reaches the installed Symbol, the install is inert — this is the make-or-break.**
- **VI-3.** For 2-arg casts (post R2-codegen), the generalized `substitution_slot=0` capture faithfully records
  `other_children=[width_symbol]` so install reconstructs `IntBin(a_symbol, width)`.

## 7. Critical files
- `prattail/src/wpda_walker.rs` (merge-drop `:10349-10466`; Sig-A landing `:4420`; Step-A `:4843-4884`; realize
  `:4555/:4711/:5305`; EOI resolve `:4000` + NEW `install_cohort_continuations`; revive+gate `:8611/:8690`; cohort
  lifecycle `:13185-13469`; chain gate `:12547`)
- `prattail/src/cohort_continuation.rs` (the dead asset — capture at pause, install at EOI)
- `prattail/src/dispatch_cohort.rs` (`deferred_continuations` `:239/:274`; `resolve()` preserve `:504/:514`;
  pause/drain `:584/:681/:818`)
- `prattail/src/sppf.rs` (`intern_symbol:535`/`intern_packing:560`/`link_packing_to_symbol:672`/`packings_of:727`)
- `macros/src/gen/runtime/wpda_codegen/prefix.rs` (G2a/R2 recognition `:1076-1197`; `CrossCatLhs:1433-1453`)
