# Float Cross-Cat Projection — Closing the Cast Family's Last 2 Tests (the 4th layer)

**pgmcp experiment #9 (continuation) · 2026-06-01 · DESIGN (Plan-agent-confirmed generalized solution)**
Targets: `test_nested_float_float_int` (`languages/tests/calculator.rs:1054`, `float(float(10,64),64)` → `10.0`) and `test_triple_nested_float` (`:1059`, `float(float(float(10,64),64),64)` → `10.0`).
Base: `6507b9c` + `/var/tmp/suite-green/sigb-cast-family-FINAL.patch` (≡ tag `sigb-b3-span-FINAL` → `d2d9a3b`, Bool-closed cast family). Verified live: calc **213 passed / 3 failed** (3 = the 2 Float targets + pre-existing `test_bool_from_list_elem`); gauntlet **4221/0**; `int(int(5,32),32)`, `int(float(10,64),32)`, `int(y != true > x < "qua")` GREEN.

---

## §0 Residual statement and scope

The cast family is split-closed on the base: Bool CLOSED (M7.1 span-anchored revival, `:2188`); the Float subset STOPPED — exactly two tests remain red. **Three prior Float fixes were FALSIFIED by their own inert diagnostic gates and MUST NOT be re-proposed:** span-anchored revival (M7.2 — no Float body to anchor), coercion-splice (M6.0, B-class), and **fold Symbol-dedup / trigger-anchored `lo_pos` (Option D, M8.1 R3 — the dedup-distinction was achieved but is NOT the blocker, and it regressed `test_nested_float_int_arithmetic`).** This plan is the **4th-layer** fix grounded in the M8.1 re-localization to the FORWARD CROSS-CAT PROJECTION layer, now confirmed + deepened with decisive live evidence (§1).

**Out of scope / must not regress:** Bool win (`:2188`), the 3 M3.1 sentinels (`cross_cat_dispatch_chaining`, `cross_cat_with_floats`, `test_nested_int_int`), **`test_nested_float_int_arithmetic` (Option D regressed it — must stay GREEN)**, `test_nested_int_float`, `cross_cat_with_parens/strings/floats`, the 4 `parse_int_cross_cat_comparison_*`, gauntlet 4221/0, op-suites ≥1331/532, soundness/`-3!`/parity, chain Welch wins.

---

## §1 Verified PHASE-1 mechanism (the spec the fix must satisfy)

**All claims below are confirmed by live build+trace on the base (`6507b9c` + FINAL patch).**

### 1.1 The defect is NOT a dispatch/codegen asymmetry — `ProcInt` and `ProcFloat` ARE emitted identically
- `ProcInt . i:Int |- i : Proc` (`calculator.rs:100`) and `ProcFloat . f:Float |- f : Proc` (`:101`) are BOTH `AtomicShape::CrossCatProjection` (sp.len()==1, source≠result, `classify_atomic` `:220-236`). Both fold into the SAME `unified_buckets` via the Pass-2a loop (`prefix.rs:1085-1119`), emitted via `emit_unified_arm` at `BP_TIER_CROSSCAT_PROJECTION`.
- In Proc context (cat 0) both dispatch arms are structurally identical 5-way Forks of `CrossCatDelegate`: the `int` arm (`wpda.rs:2359`) and the `float` arm (`:2799`). Both literal-token arms exist (`Integer`→Proc `:2074`; `Float`→Proc `:2535`). Fold-entry Forks byte-isomorphic (Float cat 5 `:1443`; Int cat 2 `:1547`), both `consume_trigger:true`.
- `single_hop_coercion` (generated) is symmetric for the load-bearing pairs: `(Float=5→Proc=0)=(0,1)=ProcFloat`; `(Int=2→Proc=0)=(0,0)=ProcInt`.

**Conclusion:** projection enumeration, dispatch arms, FIRST sets, fold Forks, and the coercion table are all symmetric. The defect is a **runtime convergence / cohort-resolution asymmetry**, not "ProcFloat isn't emitted."

### 1.2 The blocker is exclusively the OUTER fold producing Float — pinned by an isolation matrix
Probe `b3_m70_one … term`:

| Input | Outer fold → cat | Result |
|---|---|---|
| `int(int(5,32),32)` | int→Int | OK |
| `int(float(10,64),32)` | int→Int | OK |
| `uint(uint(5,32),32)` | uint→UInt32 | OK |
| `fixed(fixed(1.0p1,32),32)` | fixed→Fixed | OK |
| `float(uint(5,32),64)`, `float(bigint(5),64)`, `float(sin(1.0),64)`, `float(3+4,64)`, `float(bool(1),64)`, `float("5",64)` | float→Float | OK |
| **`float(int(5,32),64)`** | float→Float | **ERR** |
| **`float(float(10,64),64)`** | float→Float | **ERR** |
| standalone `float(10,64)`, `float(10.0,64)` | float→Float | OK |

Inner content is IRRELEVANT: `float(int(5,32),64)` fails (inner is a *passing* int fold); `int(float(10,64),32)` passes (inner is the *failing-standalone-as-operand* float fold). **The failure fires iff the OUTER fold result is Float AND its `a:Proc` operand is itself a keyword-prefixed cross-cat term whose result is Int or Float** (the two categories that begin a 5-way-ambiguous cast keyword). (`float([5],64)` also ERRs but is a separate `ElemList` issue, out of scope.)

### 1.3 It is a cohort body-resolution / crosswrap-drain asymmetry — pinned by cohort-cache stats
`PRATTAIL_WALKER_STATS=1`:
- **INT `int(int(5,32),32)` (PASSES):** `crosswrap_drained_pairs=56`, **`inflight_orphan_members=0`**.
- **FLOAT `float(float(10,64),64)` (FAILS):** `crosswrap_drained_pairs=16`, **`inflight_orphan_members=257`** (UNDRAINED).

`SIGB_CROSSWRAP=1` pairing trace: the INT scan registers a cohort member at the OUTER operand position **pos:2** with `wrap:(0,8)`=ProcBigInt and **members=11** (drainable); the FLOAT scan registers **NO non-empty member at pos:2** for the outer FloatBin operand (its pos:2 entries are `wrap:(1,12)/(1,14)/(2,16)` with **members=0**). `take_span_anchored_outer_cast` Pass-1 collects **0 Float bodies**. Both forward fanouts terminate identically (`step≈50 → Error`); Int's success comes from the `parse_via_wpda_all` cohort/crosswrap path (single-result `Int::parse` FAILS on `int(int(5,32),32)`), so both rely on the SAME crosswrap-drain machinery — Int's drains, Float's does not.

### 1.4 ROOT CAUSE — Int is rescued by an INCIDENTAL multi-hop projection redundancy that Float lacks
- **Int** projects into THREE categories: `ProcInt` (Int→Proc, `:100`), `IntToBigInt` (Int→BigInt, `:128`), `IntToBigRat` (Int→BigRat, `:129`); plus BigInt→Proc (`ProcBigInt :108`), BigRat→Proc (`ProcBigRat :109`). An inner Int-producing fold reaches Proc via **three readings**.
- **Float** projects into exactly ONE category: `ProcFloat` (Float→Proc, `:101`). No `FloatToBigRat`/`FloatToX` chain. One reading only.

The crosswrap drain needs a `DispatchCacheEntry::Resolved` body with a live (non-terminal) worker snapshot spanning the inner fold `[2,8]`, whose `body_cat` is single-hop-coercible to the paused member's `tgt_cat`. For Int, the **redundant** BigInt reading (inner `int(5,32)`→Int→IntToBigInt→BigInt) survives as a Resolved CrossCatDelegate body at pos 2 (the observed `wrap:(0,8)`=ProcBigInt, members=11) and drains. For Float, the **sole** ProcFloat reading is parsed via the same-cat FloatBin Fork inside the `a:Proc` delegate and never transitions InFlight→Resolved with a live body at pos 2 (stays among the 257 orphans), so Pass-1 collects nothing and clause-4's `single_hop_coercion(Float→Proc)=ProcFloat` never has a body to interpose over.

**The defect: the cross-cat splice of a fold-result operand depends on the INCIDENTAL existence of a multi-hop projection chain in the source category, instead of always firing for the DIRECT single-hop `cat→Proc` projection of a resolved inner fold.** Float is the one category that is BOTH a 5-way cast keyword AND has no projection redundancy.

**Spec the fix must satisfy (symmetric, upstream, evidence-only):** when an inner sub-parse RESOLVES to category `C` over `[lo,hi]` and a paused cohort member `K_sib` delegated at `pos==lo` whose `tgt_cat` is single-hop-coercible from `C` (via the existing `single_hop_coercion`), that resolved `C`-body MUST be collectible as a `take_span_anchored_outer_cast` Pass-1 body (and/or `take_pending_for_drain_crosswrap` body) so the EXISTING crosswrap splice interposes the single-hop projection and drains the member — WITHOUT relying on any multi-hop chain, WITHOUT narrowing the Fork set, WITHOUT weight/threshold. Uniform for ALL `cat→Proc` (and analogous) projections, not `float`-only.

---

## §2 Solution space + recommended generalized fix

### Rejected
- **A — synthesize a Float body (M7.2 retread):** invents a derivation; evidence-only violation. REJECTED.
- **B — weight/threshold the Fork toward FloatBin:** premature disambiguation; breaks `float(float(3))`. REJECTED.
- **C — trigger-anchored fold `lo_pos` (Option D, M8.1):** FALSIFIED, wrong layer. REJECTED.
- **D — add `FloatToBigRat`/`FloatToBigInt` to the DSL** to replicate Int's redundancy: a per-grammar DSL patch that changes the AST/display roundtrip for every language and only masks the real defect. REJECTED as non-principled.

### RECOMMENDED — Option E: collect the DIRECT single-hop projection of a resolved inner body, at the cohort-resolution layer
Generalize the EXISTING `take_span_anchored_outer_cast` / `take_pending_for_drain_crosswrap` body-collection (`dispatch_cohort.rs`) so a resolved inner body of category `C` is eligible to splice a paused member at `pos==lo` whenever `single_hop_coercion(C, tgt_cat)≠∅` — independent of whether `C` reached the cohort via a same-cat Fork or a CrossCatDelegate, and independent of any multi-hop chain. Reuses the shipped coercion machinery + the shipped revive entry; adds NO disambiguation policy, NO Fork branches.

The root sub-defect is narrow: the inner Float fold resolves as a same-cat FloatBin Fork body but is NOT registered as a `DispatchCacheEntry::Resolved` cohort body keyed at the outer operand `pos` (remains an InFlight orphan), so Pass-1's Resolved-scan never sees it. Two shapes:

**E1 (PREFERRED) — promote the resolved same-cat fold body into the cohort `Resolved` inventory so Pass-1 collects it.** At the worker pop that resolves a `CrossCatDelegate{source=C}` operand sub-parse (`cache.resolve(key, symbol_id, hi, pos_at_dispatch, snap)`, `dispatch_cohort.rs:582`), ensure the resolution registers a Resolved entry with the SPPF `symbol_id` of the inner fold result + a **live** worker snapshot — even when the inner result was produced by the same-cat fold Fork rather than a nested CrossCatDelegate. The gap is that the inner FloatBin's resolving snapshot is filtered as `is_terminal()` (Pass-1's `!s.worker_inner_state.is_terminal()` live-filter) OR the inner fold's pop never reaches `resolve()` for the outer-operand key. Fix: when a worker resolves a fold result of category `C` at `[lo,hi]` and there exist paused members `K_sib` with `K_sib.pos==lo` and `single_hop_coercion(C, K_sib.tgt_cat)≠∅`, register/retain `(symbol_id, [lo,hi], C, live-snapshot)` as a Pass-1-collectible body. Minimal, surgical, **symmetric by construction** (keyed on `single_hop_coercion`).

**E2 (FALLBACK) — add a span-anchored Symbol body source to Pass-1.** Extend Pass-1 to also scan the SPPF arena for any realized Symbol of category `C` over `[lo,hi]` with `lo==K_sib.pos` for some paused `K_sib` where `single_hop_coercion(C, tgt_cat)≠∅`, synthesizing a body from it. Bounded (one scan keyed by paused-member positions), evidence-only (splices only genuine realized Symbols). Preferred only if E1's resolution-site snapshot proves unavailable.

**Why E beats the alternatives:** it operates on the EXACT layer the M8.1 falsification re-localized to (cross-cat projection / cohort resolution), not the SPPF `lo_pos`. Reuses `single_hop_coercion` (already symmetric across all `cat→Proc`) + `revive_cohort_member_with_snapshot` (existing splice). Generalized: any future cast-keyword category without projection redundancy gets the same drain. Does NOT narrow the Fork set, NOT weight/threshold; `Ambiguous` stays first-class (`float(float(3))` still surfaces both readings — the splice only ADDS the projected reading). Addresses the upstream root (the splice's dependence on chain redundancy), not the `float` symptom.

**Token-soundness:** preserved via the EXISTING realize-time `min_terminal_span` + `slack < min_span` filter. The splice interposes `ProcFloat` (single-arg, `min_terminal_span=0`) over a genuinely-realized inner Float Symbol; no token fabricated. `crosswrap_drained` take-once keeps it idempotent.

**Welch-neutrality:** reached only when paused cross-cat members with a coercible resolved body exist — empty for cast-free chains (the R4 guard). N≥51 panel confirms.

---

## §3 Termination argument
1. No new unbounded loop — E adds body-collection eligibility inside the existing passes (or one bounded SPPF scan in E2). Fanout/revival loops + `MAX_REVIVAL_ROUNDS=4` unchanged.
2. Take-once idempotence — every spliced `(K_sib, body.symbol_id)` enters the monotone `crosswrap_drained` set (clause-5); each pair splices at most once; set ≤ O(tokens²)/parse.
3. Bounded body inventory — E1 adds ≤1 Resolved body per resolved inner sub-parse; E2's scan is one finite arena pass keyed by the finite paused-member set. No recursion beyond input nesting (`test_triple_nested_float` is the depth probe).
4. Revival budget intact — reuses `revive_cohort_member_with_snapshot` (no change to `revive_orphaned_cohort_members_once`/`MAX_REVIVAL_ROUNDS`/`SPURIOUS_ORPHAN_THRESHOLD=256`). C-bis cycle handling untouched.
5. Empirical bound — targets terminate <1 s pre-fix; post-fix the Float splice must complete in comparable steps to Int's (Int drains 56 pairs, exits cleanly, well under `PRATTAIL_MAX_STEPS=3000`).

---

## §4 Invariants carried
- **WPDS end-to-end disambiguation:** E collects a GENUINE resolved body + splices the EXISTING single-hop projection — never narrows the alternative set, never weights/thresholds. `Ambiguous` first-class (`float(float(3))` preservation test, M*.2).
- **Token-soundness via `min_terminal_span`:** the realize-time slack filter stays authoritative; the splice interposes a real projection over a real Symbol.
- **Welch-neutral on cast-free chains:** changed body-collection unreached by chains — same R4 guard. N≥51 panel at the perf gate.
- **A/B disable lever `B4_PROJ_DRAIN_DISABLE`** (parallel to `b2_crosswrap_disabled()` / `b3_span_disabled()` `wpda_walker.rs:113`): set ⇒ base (2 Float targets ERR); unset ⇒ fix active. `B3_SPAN_DISABLE`/`B2_DISABLE` continue to flip Bool/forward-drain.
- **Preserve everything closed:** Bool `:2188`, 3 M3.1 sentinels, **`test_nested_float_int_arithmetic`** (Option D's regression — E does NOT touch `lo_pos` or the slack arithmetic on the converging path), `test_nested_int_float`, `cross_cat_with_parens/strings/floats`, the 4 `parse_int_cross_cat_comparison_*`, gauntlet 4221/0, op-suites ≥1331/532, soundness/`-3!`/parity, C-bis.

---

## §5 Milestones (ONE worktree; serial FOREGROUND builds, each wrapped in `systemd-run --user --scope -p MemoryMax=32G`; 16G/8G per test; self-clean; multi-session OK)

**Setup:** worktree off `6507b9c`, `git apply /var/tmp/suite-green/sigb-cast-family-FINAL.patch` (+ `cp Cargo.lock`). **Verify base:** `int(y != true > x < "qua")` PARSES; calc **213/3**; gauntlet **4221/0**; `int(int(5,32),32)`/`int(float(10,64),32)` GREEN; the 2 Float targets ERR.

**M*.0 — DIAGNOSTIC-CONFIRM gate (INERT; STOP if falsified).** Reproduce §1.3–1.4 before any behavioral change:
- (a) Add an INERT, env-gated (`SIGB_PROJ_DRAIN`) READ-ONLY diagnostic in `take_span_anchored_outer_cast` Pass-1 logging, for `float(float(10,64),64)` vs `int(int(5,32),32)`: the collected `bodies` (symbol_id, `[lo,hi]`, `body_cat`) AND, for every paused `K_sib` with `K_sib.pos==lo`, whether `single_hop_coercion(body_cat, tgt_cat)≠∅`. **Confirm:** INT collects a body `body_cat∈{Int=2, BigInt=6}` over `[2,8]` coercible to `Proc` for the pos-2 member; FLOAT collects **NO body over `[2,8]`** for the outer operand even though `single_hop_coercion(Float=5→Proc=0)=ProcFloat` exists. **STOP if a Float `[2,8]` body IS already collected** (mechanism falsified → re-localize).
- (b) Confirm via `PRATTAIL_WALKER_STATS=1` the orphan asymmetry (INT 0 orphans/56 drained; FLOAT 257/16) + the §1.2 isolation matrix (`float(int(5,32),64)` ERR, `int(float(10,64),32)` OK). **Mechanical:** byte-identical calc 213/3, gauntlet 4221/0.

**M*.1 — Implement Option E (gated `!B4_PROJ_DRAIN_DISABLE`).** Land E1 (preferred) in `dispatch_cohort.rs` resolution/Pass-1 body-collection; fall back to E2 (bounded SPPF-arena body scan) if the resolution-site snapshot is unavailable. The new body flows through the EXISTING clauses 2–5 splice (which already carries the `ProcFloat` coercion). **GATE:**
- `float(float(10,64),64)` → `10.0` and `float(float(float(10,64),64),64)` → `10.0` GREEN.
- All §0 protected items GREEN, esp. **`test_nested_float_int_arithmetic`**, the 3 M3.1 sentinels, Bool `:2188`, `test_nested_int_float`, `cross_cat_with_parens/strings/floats`, the 4 `parse_int_cross_cat_comparison_*`.
- `B4_PROJ_DRAIN_DISABLE=1` ⇒ both Float targets ERR (base restored); unset ⇒ GREEN. `B3_SPAN_DISABLE=1` Bool unchanged; `B2_DISABLE` flips forward-drain.
- calc **215/1** (213 + 2 Float; remaining 1 = pre-existing `test_bool_from_list_elem`), gauntlet **4221/0**.

**M*.2 — Full sweep + Welch + soundness + ambiguity preservation.** op-suites `gen_calculator_op` ≥1331 / `gen_rhocalc_op` 532; `-3!` ladder + `wpda_parity_calculator`; soundness/parity; C-bis; **chain Welch N≥51 (p<0.05, quiet) Welch-neutral**; the M7.3 tests still pass. ADD: (i) a Float-family termination test mirroring `sigb_b3_span_anchored_termination_bool`; (ii) an **ambiguity-preservation** test asserting `float(float(3))` still surfaces both readings (splice ADDS, not replaces); (iii) a **generality** assertion that the same drain fires for ≥1 non-`float` `cat→Proc` projection of a resolved body. Final SPLIT→**UNIFIED** verdict (Bool + Float both CLOSED). Save FINAL patch + delta; commit + tag.

---

## §6 Gates (every milestone)
- gauntlet `-p mettail-prattail --lib` → **4221/0**.
- calc full → **215/1** at M*.1+ (213/3 at M*.0).
- op-suites: `gen_calculator_op` **≥1331**, `gen_rhocalc_op` **532/0**.
- disambiguation: `-3!` ladder + `wpda_parity_calculator`.
- Welch (chain bench, N≥51, p<0.05, quiet) — **only at M*.2**.
- A/B: `B4_PROJ_DRAIN_DISABLE` flips the 2 Float targets; `B3_DISABLE`/`B3_SPAN_DISABLE` flip Bool; `B2_DISABLE` flips forward-drain.
- Isolation regression watch: re-run the §1.2 matrix; `float(uint/bigint/sin/+/bool/str/…)` and `int(int/float/…)` MUST remain OK.

---

## §7 Risks
- **R1 — over-collection.** Clauses 2 (`EquivKey`), 3 (`span_lo==K_sib.pos`), parens-inner-steal (`sib_hi≥body.hi` exclude), 4 (`single_hop_coercion`≠∅), 5 (take-once) all still apply — E only widens which RESOLVED bodies Pass-1 *sees*, not the eligibility predicate; realize `min_terminal_span` rejects token-unsound results. A/B + full matrix re-run.
- **R2 — `test_nested_float_int_arithmetic` re-regression.** E does NOT touch `lo_pos`/slack; only adds a body to the crosswrap inventory. Explicit GREEN gate; if it regresses, scope new eligibility to bodies whose `K_sib.wrap_*` is a multi-arg fold operand.
- **R3 — neither convergence NOR drain closes it.** If E1's resolution site never has a live Float snapshot AND E2's SPPF scan finds no realized Float Symbol over `[2,8]`, the inner fold isn't realized as a Float Symbol under outer-Float context → STOP and reassess (no force/weight/threshold). Base evidence (`int(float(10,64),32)` realizes the inner Float) makes this unlikely.
- **R4 — Welch.** Unlikely (block unreached by chains); N≥51 panel; if non-neutral, gate strictly behind the `!pending_cohort_drain_keys.is_empty()`/paused-member precondition.
- **R5 — triple-nested depth.** Confirm body-inventory + take-once scale linearly (one body + one drained pair per level).
- **R6 — generality under-delivery.** If E only fixes `float`, it violates the mandate. M*.2 non-`float` generality assertion; the impl MUST key solely on `single_hop_coercion` + span/equiv, never a category id.

---

## §8 Critical sites
- `languages/src/calculator.rs:100-110` (`ProcInt`/`ProcFloat`/… — the asymmetry: Int also has `IntToBigInt :128`/`IntToBigRat :129` multi-hop redundancy; Float has ONLY `ProcFloat`), `:230-243` (4 unary `int`/`float` casts each; `uint`/`fixed` none), `:377/383` (`IntBin`/`FloatBin` 2-arg folds).
- `prattail/src/dispatch_cohort.rs` — **PRIMARY FIX SITE.** `take_span_anchored_outer_cast` Pass-1 body-collection (`for (r_key, r_entry) in self.entries { … DispatchCacheEntry::Resolved … }` + the `!s.worker_inner_state.is_terminal()` live-filter); clauses 2–5 (`span_lo==K_sib.pos`, `EquivKey`, parens-inner-steal `sib_hi≥hi`, `single_hop_coercion(body_cat,tgt_cat)`, `crosswrap_drained` take-once); `resolve()` InFlight→Resolved (`:582`); `register()` (`:526`); `take_pending_for_drain_crosswrap` (forward drain, symmetric path); `crosswrap_drained`/`crosswrap_splices_total`; `sigb_crosswrap_trace()` gate (`:51`).
- `prattail/src/wpda_walker.rs` — `single_hop_coercion` (`:334`, generated `(5,0)→ProcFloat(0,1)`, `(2,0)→ProcInt(0,0)`); forward-drain caller (`!b2_crosswrap_disabled()` → `take_pending_for_drain_crosswrap` → `revive_cohort_member_with_snapshot`); EOI revival caller (`:4170`/`:10443`, `!b3_disabled() && !b3_span_disabled()` → `take_span_anchored_outer_cast`); `revive_cohort_member_with_snapshot` (`:4480`, splice entry — REUSE); realize `slack < min_span` + `min_terminal_span`; `b3_span_disabled()` (`:113`)/`b2_crosswrap_disabled()` (A/B lever pattern for `B4_PROJ_DRAIN_DISABLE`).
- `macros/src/gen/runtime/wpda_codegen/prefix.rs` — `classify_atomic` CrossCatProjection arm (`:220-236`), Pass-2a fold (`:1085-1119`), `emit_unified_arm` (`:1456-1487`/`:1576-1601`) — confirms ProcInt/ProcFloat emitted IDENTICALLY (read-only; NO change here — the fix is runtime).
- `macros/src/gen/runtime/wpda_codegen/engine_impl.rs:1812` — `single_hop_coercion` codegen (symmetric table; read-only).
- `languages/examples/b3_m70_one.rs` (base) — `… term` probe + `PRATTAIL_WALKER_STATS`/`SIGB_CROSSWRAP` driver for M*.0 re-confirmation + the §1.2 isolation matrix.
