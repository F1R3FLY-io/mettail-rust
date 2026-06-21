# Sig-B GLL-Descriptor Redesign — progress-aware cross-cat cycle-defense + EquivKey cohort revive/splice (2026-05-31)

**pgmcp experiment #9.** Supersedes the *scope* of `sigb-cycle-defense-keying.md` (the rejected key-symmetry
design — see #9 artifacts 3/4/5 + `/var/tmp/suite-green/sigbfix-chain-cohort-DIAGNOSIS.md`). Evidence-grounded
(runtime trace + binary-search + A/B env-gating), theory-backed (Scott & Johnstone, "GLL Parsing", ENTCS
253(7):177-189, 2010, §3). Design only.

## 0. Why a `(pos,cat,bp,wrap)` heuristic provably CANNOT close Sig-B
The rejected fix (`/var/tmp/suite-green/sigbfix.patch`, u64→u128 wrap-widen of the 4 B14-C5 sites) closes only 1/5
Sig-B (`cross_cat_dispatch_chaining`) and REGRESSES `cross_cat_with_parens`. The two are in provable tension under
ANY position/wrap key: `cross_cat_with_parens` (`int((-0.5<0.5)<=b!="hh")`) needs a same-`(pos,cat,bp,W)` re-entry
**CAUGHT** (the H1' no-progress live-lock, commit `4668720`); `cross_cat_dispatch_chaining`
(`int(-220439700>1827376848==c!=-0.5)`) needs the same re-entry **ALLOWED** (a legitimate SPPF-progress fold).
Identical tuples ⇒ no position/wrap key separates them. The literature discriminator is SPPF/progress state: a
GLL descriptor is `(L,u,i,w)` with `w`=SPPF node; the current B14-C5 key is `(pos,cat,bp)` = `(L,u,i)` MISSING `w`.
Corroboration the codebase already accepts this axis: `ConfigKey` carries `sppf_top` as `w` (`wpda_walker.rs:2110-2128`,
Scott-Johnstone, `-3!`-falsified); the H1' detector uses `arena.len(sppf_stack_id)` as its progress signal (`:3876`).

## 1. Blocker 1 — cross-cat cycle-defense = progress-aware GLL descriptor uniqueness (Option a)
**Descriptor** (all fields exist on `BranchCursor`/`WpdaGss`/the SPPF-stack arena):
`ProjDescriptorKey { gss_node:u32 (cursor.node), sppf_stack:u32 (cursor.sppf_stack_id), cat_src:u16, cur_bp:u8 }`
(12 B, Copy, no Arc). `sppf_stack_id` is a `Copy u32` into the interned, **structurally-dedup'd** `PathTreeArena`
(`path_tree_arena.rs:32`, `sppf_stack_arena.rs`; proven by `property_equal_push_sequences_dedup` /
`property_distinct_permutations_distinguish`): two cursors with identical pushed-SppfId chains share the SAME
`StackId`. ⇒ a no-progress re-entry (parens) reproduces the descriptor → **cycle, drop**; a chaining fold pushes ≥1
reduced Symbol → distinct `StackId` → distinct descriptor → **allowed**. `pos` is intentionally DROPPED (redundant at
a fixed dispatch; `sppf_stack_id` is the discriminator).
**New helper** `extract_proj_descriptor(cursor,gss)` (replaces `extract_dispatch_config:2710` at the cross-cat sites).
**New per-cursor field** `visited_proj_descriptors: im::OrdSet<ProjDescriptorKey>` (cross-cat-only; empty on chains →
Memory Option A). Keep `visited_recovery`/`PackedDispatchConfig` UNCHANGED (recovery is not the blocker).
**5 sites to convert** (`wpda_walker.rs`): (1) singleton Push `:5856-5877`; (2) Fork pure-projection drop `:6668-6699`
(error msg → report sppf_stack); (3) Fork per-branch skip `:6783-6788` (keep `&& is_cross_cat_delegate_branch`); (4)
H1' broadening insert `:6760-6768` (insert PARENT's descriptor — carrying parent `sppf_stack_id` — into all non-recovery
children: parens re-enters with same StackId → caught; chaining re-enters with advanced StackId → allowed; THE crux);
(5) Tomita B12 broadcast `:9177-9189` (materialize from the arc's shell). Plumb the field through BranchCursor
ctors/clones (`:1498,1806,1910,1982,3611,5691` + Fork-child arms `:6871,6971,7047,7116,7217,7298,7380`),
`allocate_fork_push_child` params (`:13255`), and `CohortShell`/`CohortMemberState` carry-through (`cohort_lazy.rs`).
**Invariant:** drop fires ONLY on descriptor reproduction (= provable no-progress cycle); progress ⇒ distinct ⇒
survives to EOI/cohort/Step-A. No heuristic; EquivKey untouched; Ambiguous first-class; genuine cycles still caught
(true re-projection reproduces StackId — LedTest Pred↔Num projection-cycle tests `:6651` must stay green).
**Rejected (b) delete+delegate-to-cohort:** the cohort is keyed on the dispatch SITE not the descriptor's progress,
is not a cycle oracle, and would re-expose the rhocalc `and_tt` live-lock on non-cross-cat paths.

## 2. Blocker 2 — cohort revive/splice = EquivKey-quotiented cross-revive
**Root cause** (`int(a<b<=0.5)`): the outer cast enters `BinderRule{Int,cast}` awaiting its Bool body. M4 widens
`DispatchKey += {wrap_cat=category_src_idx, wrap_rule=rule_index_in_category}`. The body worker RESOLVES popping a
`CrossCatProjection` edge with wrap W_resolve (`<=`); the PAUSED cast member sits under K_pause with wrap W_pause
(`<`). `take_pending_for_drain` (`:553`) keys on the FULL `DispatchKey` → K_resolve≠K_pause → K_pause never drains →
the cast body never splices → cursor stuck in `BinderRule` → `is_accepting_config` `_=>false` (`:5486`) →
`accepting_indices=0` → "no accepting branch ... '('" (`:4323`). `revive_orphaned_cohort_members_once` (`:8707`)
can't rescue (MAX_REVIVAL_ROUNDS=4 + re-collision; and it re-RUNS the body rather than SPLICING). `SIGB_NO_COHORT`
fixes the minimal case (disables the pause).
**Fix:** trigger the drain over the cohort-MERGE `EquivKey=(source_src_idx,inner_cur_bp)` bucket (`dispatch_cohort.rs:108`,
which DELIBERATELY drops wrap) while keeping the CACHE keyed on full `DispatchKey` (M4 un-conflation intact). New
`take_pending_for_drain_equiv(equiv, &resolved)`: for each entry sharing the EquivKey AND `entry.pos==resolved.pos_at_dispatch`,
revive its paused members against the just-resolved worker's snapshot via the existing `revive_cohort_member_with_snapshot:13490`
(the member re-pushes `CategoryEntry(source_src_idx)` with its OWN return_frame ⇒ the cast rule consuming the body is
the member's). Resolve-site trigger at `cursor_gss_pop_via_edge:14039`; drain-loop revive at `:9501`. Fires at the
NORMAL end-of-step drain (NOT the EOI orphan path) ⇒ no MAX_REVIVAL_ROUNDS/spurious-gate interaction; bounded by
`MAX_PENDING_COHORT_PER_KEY=16` × EquivKey-sharing-entries-at-pos (grammar-bounded). Closes nested-paren (`le`,
`original_6`) + Bool-lit/Str (`bool_prefix_tokens`) — same K_resolve≠K_pause split (trace-checkpoint if residual:
the symmetric "revive-on-pause-against-already-Resolved" at `pause_cohort_member:834`).
**Invariant:** ADDS revived cursors (more complete, never drops); EquivKey is a grammar-determined equivalence (not a
weight); EquivKey stays narrow (READ for revive, NOT widened; cache stays full-key); Ambiguous preserved (each
resolving packing cross-revives → multiple accepting cursors).

## 3. Memory = Option A (chains byte-identical)
Do NOT widen `PackedDispatchConfig` (stays u64). `visited_proj_descriptors` is a SEPARATE cross-cat-only set, empty on
chains → `im::OrdSet::clone()` of empty = O(1) Arc-bump → zero chain RSS (Welch already showed u128 loses right_50/100/200
+10.8/+5.4/+4.1% p<0.05). Blocker 2 adds no per-cursor field (operates on the walker-global cohort cache). R4 fallback:
`Option<im::OrdSet<...>>` (None on chains) if even the empty-OrdSet Arc regresses.

## 4. Milestones (ONE worktree, serial foreground --wait builds; main tree NEVER modified)
- **M0** — descriptor primitive + plumb (INERT; keep old checks live in parallel). Gate: gauntlet 4220/0; chain Welch NEUTRAL.
- **M1** — Blocker 1: switch the 5 sites to the descriptor; remove dead cross-cat `visited_dispatch` use. Gate:
  `cross_cat_with_parens` GREEN + `cross_cat_dispatch_chaining` GREEN + LedTest projection-cycle 0-fail + rhocalc
  `and_tt` live-lock bounded + gauntlet 4220/0.
- **M2** — Blocker 2: `take_pending_for_drain_equiv` + resolve-site EquivKey drain trigger + drain-loop revive.
  Trace-checkpoint: confirm `K_resolve.equiv()==K_pause.equiv()` for `int(a<b<=0.5)`. Gate: ALL 5 Sig-B GREEN +
  `cross_cat_with_parens` stays + 16 M4-fixed + 4 realize-fixed + `_ge`/`_ne`/`_in_expression` stay.
- **M3** — full gate sweep + Welch + ambiguity (§5).

## 5. GATES (experiment #9 acceptance)
5 Sig-B green (`parse_int_cross_cat_comparison_le`, `simulator_regression_{original_6,cross_cat_dispatch_chaining,cross_cat_with_floats,bool_prefix_tokens}`)
+ `simulator_regression_cross_cat_with_parens` green; 16 M4-fixed + 4 realize-fixed + `_ge`/`_ne`/`_in_expression` stay;
gauntlet `cargo test --release -p prattail --lib`=4220/0; C-bis cycle/newton/tarjan/star/scc/self_loop 0-fail
(Blocker 1 must NOT weaken genuine-cycle detection); op-suites gen_calculator_op≥1331/gen_rhocalc_op 532; soundness probe
+ `-3!` + `wpda_parity_calculator`; **MANDATORY interleaved Welch chain panel N≥51 + chain_1000/2000 RSS +5% max**
(Option A predicts NEUTRAL — load-bearing guard); ambiguity-preservation (genuinely-ambiguous cross-cat still `Ambiguous`).

## 6. Risks
R1 over-tighten (false progress lets a true cycle escape) → arena dedup is structural; add a synthetic pure-re-projection
regression. R2 under-tighten (productive chaining shares StackId) → the fold pushes a reduced Symbol before re-dispatch
(`cross_cat_dispatch_chaining` is the live test). R3 cross-revive at wrong pos → `pos` identity assert. R4 chain RSS →
Option A empty-set; fallback `Option<OrdSet>`. R5 EquivKey leak into cache → cache stays full `DispatchKey`; assert M4's
`int(int(5,32),32)` un-conflation count stays > M1's.

## 7. Critical files
- `prattail/src/wpda_walker.rs` (Blocker 1 sites :5856,:6668,:6783,:6760,:9177; Blocker 2 :9501 drain,:14039 resolve,
  :13255/:13490 allocate/revive; `BranchCursor:1357`, `extract_dispatch_config:2710`, `is_accepting_config:5456`,
  `resolve_at_end_of_input:4000`)
- `prattail/src/dispatch_cohort.rs` (`DispatchKey:63`/`EquivKey:108`, `take_pending_for_drain:553`, `pause_cohort_member:787`;
  new `ProjDescriptorKey` + `take_pending_for_drain_equiv`)
- `prattail/src/cohort_lazy.rs` (`CohortShell` carry-through), `sppf_stack_arena.rs`+`path_tree_arena.rs` (`StackId` interning = the `w` primitive), `gss.rs` (`EdgeKind::CrossCatProjection` wrap carry)
