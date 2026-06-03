# In-Line Forward Projection Fix — the Recursive Cursor-Driven Closure of the Cast Family's Last 2 Targets (pgmcp experiment #9, 2026-06-02)

**Base (implementation):** `d2d9a3b` (Bool-closed cast-family tree; calc 214/6 with the 2 Float targets ERR; gauntlet 4220/0; **walker = 18573 lines** — line numbers below are `d2d9a3b`, NOT HEAD `8ffd6fc` which is docs-only on the divergent `380cc94` lineage with walker = 17551 lines + different line numbers). The implementing agent works from a fresh `ifp-impl` branch at `d2d9a3b` (the `1a6bd18` forward-REGISTRATION code — tag `fwdproj-STOP-M0`, the 6th falsification — is REVERTED, not extended).

**The standing mandate (verbatim):** *"No hardcoded assumptions! We must support any pattern supported by the `language!` specification grammar!"* — every predicate keys on STRUCTURAL facts (an edge kind, a span length, a transparent-projection rule existing for a category), never a category name / keyword / lattice size / arity / rule-count.

**This is the 7th approach.** SIX falsified: A2-Fork-merge, M8.1-Symbol-`lo_pos`, M9-cohort-projection, prefix-trie/genfactor, span-anchored-revival-for-Float, forward-REGISTRATION. This design is grounded in WHY each failed (§8) and is GATED by a BLOCKING M0 FLIP-CONFIRM (§0/§6) that must EMPIRICALLY close the targets via the IN-LINE worker path BEFORE any full implementation. **If M0 cannot make a Float SPPF Symbol span `[_,11]` via an in-line worker (cohort_origin==None, NOT a revive) AND close both targets to 216/4 AND hold the must-not-perturb set, STOP and report the exact wall.**

---

## §0 — THE M0 FLIP-CONFIRM (BLOCKING, STOP-GATED, FIRST)

### §0.1 Why M0 is non-negotiable
The forward-REGISTRATION attempt (the 6th) was a designed, grounded fix that passed its own reasoning and STILL hit two walls when built: (WALL 1) it routed operand delivery through the proven-WRONG cohort REVIVE layer → the revived inner cursor carried STALE `inner_state=PrefixDispatch{pos:2}` → dropped; (WALL 2) it addressed only the inner pos-2 level (the asymmetry is RECURSIVE; the top-level pos-0 `float→Proc` was equally suppressed → no `hi_pos=11` body → `accepting_indices==0`) AND it OVER-GENERATED (regressed `parse_int_cross_cat_comparison_le` + `simulator_regression_original_6`). IFP is structurally different (in-line WORKER not revive; recursive; precisely triggered) but it is a DEEPER change to the same machinery and R1 has materialized once. **M0 de-risks it empirically.**

### §0.2 The decisive M0 claim
A scratch lever `IFP_PROBE` (UNTRACKED, env, read at walker init) makes a cast-fold operand's same-cat Proc self-projection survive as an **in-line WORKER** (`RegisterOutcome::WorkerInserted`, `cohort_origin==None`, live forward `inner_state` — NOT `revive_cohort_member_with_snapshot`) at EVERY dispatch level incl. top-level pos-0, and:
1. **(SPAN)** produces a Float SPPF Symbol spanning `[_,11]` at the top level — EOI census shows ≥1 Float/Proc cursor `pos=11 state=Accepted sppf_top_cat=0(Proc)` (mirroring INT's `i=0 pos=11 Accepted span=[4,11]`);
2. **(TARGETS)** closes `test_nested_float_float_int` + `test_triple_nested_float` → calc **216/4** (release);
3. **(NO REGRESS)** clean A/B: `IFP_PROBE=0` → exact `214/6`; `IFP_PROBE=1` → `216/4`; ONLY delta = the 2 targets. `int(str)`/`int(int)`/Bool/the 2 registration-regressed cross-cat tests HOLD.

### §0.3 STOP conditions (any ⇒ STOP, report the wall, halt)
- **(S-a)** necessary-not-sufficient: the worker fires but no Float Symbol spans `[_,11]` / targets don't close → report the level + the stall `inner_state`/`pos`/`node`.
- **(S-b)** over-generation (R1): any non-target test flips under `IFP_PROBE=1` → report the over-fired predicate instance.
- **(S-c)** new non-genuine `Ambiguous` → report the spurious root's span/cat.
- **(S-d)** termination/fan-out exceeds the INT-path peak by more than a small constant → report the unbounded site.

### §0.4 Scratch construction (tests the IN-LINE worker specifically, NOT the falsified registration)
On clean `d2d9a3b` (registration reverted): **(P1)** un-suppress the same-cat ProcFloat CrossCatDelegate branch at the GLL gate sites 1/2/3/5 ONLY when the scratch C1∧C2∧C3∧C4 (§3) holds, so it's allocated as a `WorkerInserted` cursor; **(P2)** advance the descriptor (IFP-C); **(P3)** instrument that the cursor reaching `pos=11 Accepted` has `cohort_origin==None` (in-line worker, NOT `cohort_origin=Some(..)` revive — the decisive discriminator, `revive_cohort_member_with_snapshot` always sets `Some`). Budget ≤4 incremental WALKER-only builds (warm cache; same-binary runtime A/B).

### §0.5 M0 RESULT — **STATUS: PENDING** (filled by the implementing agent before §1-§9 is trusted): (SPAN) the Float EOI census line; (TARGETS) the 216/4 faillist diff; (NO REGRESS) the IFP_PROBE A/B faillist; (P3) the cohort_origin==None confirmation. If any §0.3 STOP fires, record the wall and halt.

---

## §1 — The INT in-line continuation path (GROUNDED) — the breakthrough

### §1.0 Token layouts
`float(float(10,64),64)`: `0=float 1=( 2=float 3=( 4=10 5=, 6=64 7=) 8=, 9=64 10=) 11=EOI` (inner FloatBin `[4,8]`; outer needs `[_,11]`). `int(int(5,32),32)` isomorphic.

### §1.1 The worker-vs-member dichotomy (the load-bearing distinction the 6th attempt missed)
`allocate_fork_push_child` (`:14076`) consults `dispatch_cohort_cache.register(key,…)` (`:14143`) for every `CrossCatDelegate` branch:
- **`RegisterOutcome::WorkerInserted`** (the FIRST cursor at a `DispatchKey`): falls through to normal allocation (`:14280`) → pushes a `CrossCatProjection` edge (`:14325`) → a **LIVE in-line cursor** parsing the sub-parse forward; `inner_state` is live; `cohort_origin` stays `None`.
- **`RegisterOutcome::InflightCollision`** (later cursors at the same key): PAUSED as a `CohortMember{return_frame,…}` (`:14160`); revives only at end-of-step via `revive_cohort_member_with_snapshot` (`:14480`) which sets `cursor.pos=hi_pos`, `cohort_origin=Some(key)`, `inner_state=snap.worker_inner_state` — the STALE paused dispatch state.

When a CrossCatProjection edge pops (`cursor_gss_pop_via_edge:14990`), the `:15013` gate calls `resolve(key,…)` (`dispatch_cohort.rs:581`) which ONLY transitions the cache entry InFlight→Resolved + accumulates snapshots/paused-members — it does NOT touch the popping WORKER cursor. The worker continues its OWN forward pop processing in-line (its `node`/`pos`/`inner_state` advance into the outer rule's continuation). `FirstResolve→pending_cohort_drain_keys` only fans the OTHER paused (stale) members.

**⇒ THE IN-LINE CONTINUATION ALREADY EXISTS — it is the `WorkerInserted` cursor.** The 6th attempt's fatal error: it delivered the operand via `pending_cohort_drain_keys→revive` (the PAUSED-member STALE path) instead of via the WORKER (the in-line LIVE path). **IFP makes Float's same-cat ProcFloat self-projection become a WORKER, exactly as INT's distinct-cat projection already is.**

### §1.2 Why INT's top-level `hi_pos=11` body forms (census `fwdproj-recover-int-census.log`)
INT revive tuples at `pos_at_dispatch=0` (TOP level): `pos_before=0 → hi_pos=11 source=6 wrap=(0,8)` **×1808** (`source=6`=BigInt, `wrap=(0,8)`=ProcBigInt) — the DOMINANT top-level body; `… source=2 wrap=(0,0)` ×113 (ProcInt, same-cat minority). INT's lattice (`calculator.rs:128-129` `IntToBigInt`/`IntToBigRat` + `ProcBigInt`) gives the top-level Int fold a DISTINCT-cat route Int→BigInt→Proc; BigInt≠Int dispatch cat → DISTINCT `ProjDescriptorKey` → escapes the GLL same-cat skip → `WorkerInserted` → CrossCatProjection pop at `pos_at_dispatch=0` → `hi_pos=11` body. EOI census: **INT `i=0 pos=11 Accepted sppf_top_cat=0(Proc) span=[4,11]`** (the worker Accepts; the 1808 revives fan paused siblings).

### §1.3 Why FLOAT's `hi_pos=11` body NEVER forms (census `fwdproj-recover-float-census.log`)
FLOAT revive tuples `pos_at_dispatch ∈ {2,4,6,9}` ONLY — **ZERO pos_at_dispatch=0**; hi_pos set `{5,7,8}` — never 10/11. Float's ONLY transparent Proc route is same-cat `ProcFloat` (`calculator.rs:104`); `Float64→{CanonicalBigRat}` is sparse with NO distinct-cat `FloatToBigRat`+`ProcBigRat` operand-position intermediary; FloatToInt/Str/Bool are trigger-prefixed (need `int(`/`str(`/`bool(`). Float's same-cat ProcFloat (`cat_src=5→Proc`) reproduces the dispatch `ProjDescriptorKey` (same `gss_node`, same `sppf_stack` — the fold Symbol isn't yet on the stack at projection re-entry, same `cat_src=5`, same `cur_bp`) → GLL-suppressed → NO worker → no pos-0 CrossCatProjection pop → no `hi_pos=11` body → EOI census: all 12 Float resolve calls `n_cursors=0 Error{"all fork branches dropped"}`.

### §1.4 The GLL suppression (5 sites)
`ProjDescriptorKey=(gss_node, sppf_stack, cat_src, cur_bp)` (`:2893`); `sppf_stack` is the progress/`w` discriminator. Sites: **1** `:6128` singleton-bucket Drop; **2** `:6964` pure-projection Fork Drop (`is_projection_fork:2759` = ALL branches CrossCatDelegate); **3** `:7094` per-branch skip (`if parent_in_visited && is_cross_cat_delegate_branch → continue` — **THIS suppresses Float's ProcFloat branch in the MIXED pos-2 Fork**, census `pure_proj_fork=false`); **4** `:7064` insert; **5** `:9919` cohort-shell per-arc B12. INT escapes (distinct `cat_src`); Float reproduces (same `cat_src=5`, pre-fold StackId).

### §1.5 The asymmetry is RECURSIVE
The suppression recurs at every level. The 6th attempt fired at `{2,4,6,7,9,10}` but NEVER pos-0; INT's rich lattice rescues the top via Int→BigInt (1808×); Float suppressed at EVERY level. **IFP must worker-ize the same-cat self-projection RECURSIVELY at every level incl. pos-0 (where `hi_pos=11` must form).**

---

## §2 — The recursive in-line self-projection mechanism

### §2.0 Structural principle (no hardcoding)
> **A cast-keyword FOLD operand whose result category needs a same-cat Proc projection (and that no distinct-cat lossless projection already covers) MUST, on the forward path, fire that same-cat Proc projection as a LIVE in-line WORKER (`WorkerInserted`, NOT a paused-member revive) at the operand dispatch — RECURSIVELY at every dispatch level — so the popping worker cursor IS the in-line outer continuation. Eligibility keys on STRUCTURAL facts (the operand-pop edge kind, the multi-token span, an existing transparent Proc projection rule, the absence of a distinct-cat covering projection), never a category name/keyword/lattice-size/arity.**

### §2.1 The changes (WALKER-only; NO codegen, NO prefix-Fork, NO revive layer)
**(IFP-A)** the precise trigger `is_starving_self_projection_operand(...)` (§3), computed at the GLL gate. FALSE ⇒ gates behave byte-identically (genuine cycle defense untouched). TRUE ⇒ admit the same-cat projection branch as a worker (IFP-B) with an advanced descriptor (IFP-C).
**(IFP-B)** un-suppress at sites 1/2/3/5 GATED on IFP-A: e.g. site 3 (`:7094`) becomes `if parent_in_visited && is_cross_cat_delegate_branch && !is_starving_self_projection_operand(branch,cursor) → continue`. The same-cat ProcFloat branch is then allocated → `register(key)` → FIRST per key = `WorkerInserted` → a live in-line cursor (NOT a paused member). Site 2 guard `!(is_pure_projection_fork_with_starving_member)`; sites 1/5 same IFP-A guard on the Drop/arc-skip.
**(IFP-C)** advance the descriptor (the M-C intent made real): at the admit point compute the descriptor with the POST-FOLD `sppf_stack` (the StackId after the fold Symbol is interned) so the worker's re-entry is DISTINCT; insert it into `child_visited_proj_descriptors` (site 4, `:7064`). The no-progress paren re-entry (same StackId, no fold) still reproduces + is skipped.

### §2.2 How the worker drives the outer continuation IN-LINE (recursion incl. pos-0)
The admitted worker: (1) parses the inner FloatBin `[4,8]` (its `inner_state` is LIVE forward — `CrossCatDelegate{source=5}` then the FloatBin body — NOT stale `PrefixDispatch{pos:2}`); (2) pops its CrossCatProjection edge at `:15013` → `resolve()` records the body AND the worker continues forward (advances into the outer FloatBin `PrefixRuleEntry{cat_src:5,rule_idx:15,…}`); (3) drives the outer `, 64 )` (pos 8→9→10) IN-LINE — what the revive could NOT do (stale). At the TOP level (pos-0 dispatch) the worker projects the whole outer fold Float→Proc as a worker → `hi_pos=11` body → Float SPPF Symbol spans `[_,11]` → `accepting_indices≥1` → PARSE-OK. **The recursion is structural** (same IFP-A trigger at whatever level presents a starving cast-fold operand): `float(float(10,64),64)` fires at pos-2 (`hi_pos=8`) AND pos-0 (`hi_pos=11`); `test_triple_nested_float` at three levels. No per-level special-casing.

### §2.3 Symmetry (INT incidental vs FLOAT structural)
| | INT (baseline pass) | FLOAT (IFP) |
|---|---|---|
| pos-2 inner | Int→BigInt (`wrap=(0,8)`, distinct) → WORKER | ProcFloat (`wrap=(0,1)`, same-cat) — suppressed → **WORKER by IFP-B** |
| pos-0 top | Int→BigInt→Proc → WORKER → `hi_pos=11` | ProcFloat same-cat — suppressed → **WORKER by IFP-B recursively** → `hi_pos=11` |
| continuation | worker (cohort_origin=None) → Accepted Proc `[4,11]` | worker (cohort_origin=None) → Accepted Proc `[_,11]` |
| descriptor | distinct cat_src (BigInt≠Int) | **IFP-C advances sppf_stack → distinct** |
| mechanism | incidental (lattice multiplicity) | structural (worker-ize the starving self-projection) |

### §2.4 NOT revive, NOT registration, NOT prefix-Fork
- **NOT REVIVE:** IFP admits a `WorkerInserted` cursor (`cohort_origin==None`); NEVER calls `revive_cohort_member_with_snapshot`/`pending_cohort_drain_keys`/`intern_coercion_over_body`. §0.4 P3 is the proof. The revive layer is UNTOUCHED (still fans genuine paused members — the Bool win path).
- **NOT registration:** no new `resolve()` registration; IFP REMOVES a suppression so the projection reaches the EXISTING `register()→WorkerInserted` path.
- **NOT prefix-Fork/lex-min/merge/span-anchor:** zero edits there → the 5-way prefix Fork is byte-identical → cannot reintroduce the trie's `int(str)` regression.

---

## §3 — The PRECISE no-over-generation trigger

### §3.1 `is_starving_self_projection_operand(branch, cursor)` — TRUE iff ALL (each structural):
1. **(C1) SAME-CAT transparent Proc projection of the dispatch category:** `branch.new_state` is `CrossCatDelegate{source_src_idx:S}` AND the pushed `symbol.category_src_idx == Proc-join-cat` AND `S == cursor`'s dispatch `cat_src`. Distinct-cat projections (Int→BigInt) → C1 FALSE → existing worker path unchanged.
2. **(C2) the operand is a cast-keyword FOLD (multi-token), not a bare atom/comparison chain:** the dispatch's pending operand is a 2+-arg binder-rule fold whose result cat == `S`, detected via the `PrefixRuleEntry`/`BinderRule` context (a rule with ≥2 `ParamParse` positions under a shared trigger + the `,`-fold lookahead) — the SAME fold-shape signal codegen's lowered `BinderShape` provides (looked up opaquely, never matching `,`/`)`/`Float`). **EXCLUDES `int(-928988166<=y<=…)` (R1 victim): a comparison chain, not a cast-fold → C2 FALSE.**
3. **(C3) genuinely multi-token span (soundness):** `span_hi-span_lo >= min_terminal_span(S,fold_rule) >= 2` — reuses the EXISTING authority (FloatBin `(5,15)=2`).
4. **(C4) NO distinct-cat lossless projection already covers:** among the dispatch Fork's branches, no admissible distinct-`cat_src` projection of `S` would worker-ize the same body. Computed from the transparent-projection set (`single_hop_coercion:331`/`lossless_targets`): if `lossless_targets(S)` has `D!=S` with `D→Proc`, the distinct route covers → C4 FALSE. **This makes IFP fire for Float (sparse: no distinct D→Proc) but NOT Int (rich: Int→BigInt→Proc).** Keys on "does a distinct-cat lossless-then-Proc route exist," never the category name.

### §3.2 Why it does NOT fire on each must-preserve case
- `int(-N<=y<=(-N<=y))` (R1 victims): comparison chain, not a cast-fold → **C2 FALSE**.
- `int(str(…))` (`simulator_regression_nested_casts`): inner Str distinct-cat cross-wrap already worker-izes → **C4 FALSE** + C1 FALSE. (IFP touches neither prefix-Fork nor cross-wrap drain → cannot regress it as the trie did.)
- `int(int)/int(float)` (`test_nested_int_int`/`test_nested_int_float`): Int's rich route covers → **C4 FALSE**; nominal same-cat ProcInt is deduped by `register()` (§4 T1).
- Bool win `int(y != true > x < "qua")`: comparison chain from bare `y`, no cast-fold trigger → **C2 FALSE** (span-anchored revival path untouched).
- `float(float(3))`/nested UNARY (`test_float_float_nested`): unary cast (single `ParamParse`), not a 2-arg fold → **C2 FALSE**. *(Also why the FLIP couldn't ship by deletion — deleting unaries broke this; IFP leaves unaries alone.)*
- `str(3)`/`bool(0)`/`float(10.5)`/`int(true)` standalone; chains/operators/collections/rhocalc/all non-calculator: no cast-fold operand → **C2/C1 FALSE** → O(1) short-circuit.

### §3.3 The positive set (where IFP fires)
ONLY a `float`/`int`/`uint`/`fixed`-FOLD operand whose result cat has NO distinct-cat lossless-then-Proc route (Float + any future sparse cast cat): `float(float(…),…)`, `float(int(…),…)` (the OUTER float fold's top-level ProcFloat is starving), recursively `float(float(float(…)))`. Matches the discriminator "failure ⟺ the OUTER is a float-FOLD whose first operand is itself a 2-arg cast fold."

---

## §4 — Termination / soundness (RIGOROUS)
- **T1 — bounded fan-out (deduped by the EXISTING cache):** ≤1 worker per `(dispatch_pos,S,ProcX-wrap)` DispatchKey (FIRST=WorkerInserted, second=InflightCollision/NoOp) — IDENTICAL to INT's bound. Peak `branch_cursors` ≤ the INT-path peak (IFP un-suppresses ONE delegate the flat-Fork already enumerated). `peak_IFP(step) ≤ peak_INT-analog(step)`.
- **T2 — GLL descriptor-uniqueness PRESERVED:** IFP-C advances `sppf_stack` (post-fold = genuine progress) → distinct descriptor; the no-progress paren re-entry (same StackId, C2/C3 FALSE for a bare paren) still reproduces + is Dropped/skipped. Scott-Johnstone uniqueness + CrossCatDelegate cycle guard (`:5859`) + bounded-recovery untouched.
- **T3 — soundness via `min_terminal_span` (UNTOUCHED + C3 gate):** projection only over a real multi-token span; realize slack filter (`:4843-4884`) rejects unsound packings independently.
- **T4 — `Ambiguous` first-class (UNTOUCHED):** a 2nd genuine root → `>=2` arm (`:4376`) → multi-root Ambiguous under cap. M0 (S-c) tripwires spurious roots.
- **T5 — recursion bounded by input nesting depth (finite):** ≤1 fire per level; IFP-C prevents re-projection at the same descriptor. `test_triple_nested_float` (3 levels) is the depth stress.

---

## §5 — Invariants (verified at §6/§7)
`min_terminal_span` (`:315`/`:4843-4884`/gen `:21599`) UNTOUCHED + C3 gate. `Ambiguous` `>=2` (`:4376`) UNCHANGED. lex-min/resolve/accepting UNTOUCHED. **REVIVE layer UNTOUCHED** (`:14480`/`:14424`/`:14381`/`pending_cohort_drain_keys` — the Bool win still routes here). **Prefix-Fork UNTOUCHED** (`binder.rs:1035` — `int(str)`-isolation). Must-not-perturb: 2 targets→PASS (calc **216/4**, 4 pre-existing non-Float remain); Bool win; 3 M3.1 sentinels; `test_nested_float_int_arithmetic`; the 5 trie-regressed + 2 registration-regressed cross-cat tests; standalone+nested unary casts; op-suites ≥1331/532; `-3!`/parity; chain Welch; gauntlet 4220/0. **A/B lever `IFP_DISABLE`** (env, runtime, same-binary A/B; DEFAULT fix-OFF on the shipped commit — `IFP_DISABLE` absent ⇒ baseline behavior is WRONG; invert: shipped default = fix-ON via absence of disable, i.e. `IFP_DISABLE=1` disables → baseline. Do NOT repeat the WIP's dangerous semantics; make `IFP_DISABLE=1` = baseline `214/6`, default = `216/4`).

---

## §6 — Milestones (M0 = BLOCKING flip-confirm-FIRST)
All builds `systemd-run --user --scope -p MemoryMax=32G cargo …`, ONE at a time, clean `d2d9a3b` (`ifp-impl` branch), WALKER-only (incremental; same-binary A/B).
- **M0 — FLIP-CONFIRM (BLOCKING; §0):** 1. baseline `214/6` + gauntlet 4220/0; reproduce the asymmetry inert (Float 0 pos-0 pops; INT `hi_pos=11`×1808). 2. build the §0.4 scratch (`IFP_PROBE`). 3. (SPAN) trace `float(float(10,64),64)` `IFP_PROBE=1`: Float `pos=11 Accepted span=[_,11]` AND (P3) `cohort_origin==None`. 4. (TARGETS+NO REGRESS) `IFP_PROBE=1` full calc → `216/4`; `IFP_PROBE=0` → `214/6`; only the 2 targets flip. STOP per §0.3 otherwise. 5. no-hardcoding inspection of C1-C4.
- **M1 — IFP-A + IFP-B** at sites 1/2/3/5, behind `IFP_DISABLE`, reusing `register()→WorkerInserted` — NO new cache/state, NO revive, NO registration.
- **M2 — IFP-C** (descriptor advance) at site 4 + `ProjDescriptorKey`; assert the no-progress paren cycle STILL fires (unit + `cross_cat_with_parens`); assert C4's lookup matches codegen's transparent-projection set.
- **M3 — targeted green (ONE build):** 2 targets + `test_triple_nested_float` PASS; `float(10.5)`/`int(true)`/`str(3)`/`bool(0)`/`float(float(3))`/`test_all_to_int`/`test_float_float_nested` PASS; `int(str)`/`int(int)`/`int(float)`/Bool/the 2 registration-regressed PASS.
- **M4 — generality + recursion sweep:** float/int/uint/fixed nested folds via the SAME worker (Float worker-izes at pos-0 AND pos-2; Int unchanged); deeper nests terminate (T5); full A/B byte-clean outside the 2 targets.

---

## §7 — Gates (all before commit)
- **calc 216/4** (RELEASE): 2 targets + `test_triple_nested_float` PASS; 4 pre-existing remain; ZERO other regressions; re-assert the must-not-perturb set.
- **A/B (dominant tripwire):** `IFP_DISABLE=1` → exact `214/6`; default → `216/4`; ONLY delta = the 2 targets (+`test_triple_nested_float`). Else STOP.
- **Welch (chain neutrality):** `IFP_DISABLE` ON vs OFF, cast-free chains, N≥51, indistinguishable (C2 FALSE on chain steps → O(1)). Any arm loss ⇒ STOP.
- **Cross-cat sweep:** `cross_cat_dispatch_chaining`/`with_floats`/`with_parens`/`with_strings`/comparison families/`in_expression`/`nested_cross_cat_str` GREEN.
- **Sweep:** op-suites ≥1331/532, `pass2c_token_soundness_probe`, `-3!` (229+23), `wpda_parity_*` 16+2, C-bis 70, gauntlet 4220/0.

---

## §8 — Risks (grounded in the 6 falsifications)
- **R1 (#1, MATERIALIZED ONCE) over-generation:** C2 excludes the comparison-chain `int(-N<=…)`; C4 excludes `int(int)`/`int(float)`/`int(str)`; C1+`register()` dedupe make a nominal Int same-cat a no-op. M0 sub-check 4 + §7 A/B is the tripwire; if any flips, STOP + narrow C2 to require the fold result cat EXACTLY equal the outer dispatch cat.
- **R2 (the flip-v1/v2/registration wall) necessary-not-sufficient:** IFP uses the WORKER (cohort_origin=None, live), NOT the revive (stale). M0 (SPAN)+(P3) is the load-bearing gate; STOP at (S-a) otherwise.
- **R3 (WALL-1 recurrence) pos-0 not reached:** IFP-A keys on operand STRUCTURE (C2) present at pos-0 exactly as pos-2 → fires recursively. M0 (SPAN) + M4 trace-confirm pos-0 firing.
- **R4 IFP-C re-opens a cycle:** advances `sppf_stack` only for genuine progress; paren re-entry still skipped (T2). M2 unit + `cross_cat_with_parens` + gauntlet.
- **R5 runtime lever perturbs non-cast hot paths:** C1/C2 FALSE on every non-cast step → O(1). Welch.
- **R6 (#1 DEPTH — narrow down-payment on Exp 15):** IFP is deeper than the prior 6. Mitigation: STRICTLY a GLL-gate un-suppression (4 guarded clauses) + descriptor advance — NO new state/action/cache/driver-rewrite; reuses the worker path INT already exercises. If M0 shows un-suppression alone can't worker-ize the same-cat projection (the branch isn't even emitted at pos-0), the wall is structural-absence → escalate to a small `prefix.rs::emit_cross_cat_prefix_unary_arm` addition (still far narrower than Exp 15). M0 must confirm the same-cat ProcFloat branch EXISTS at pos-2 (census `wrap=(0,1)` confirms pos-2; pos-0 is M0's open question).

---

## §9 — Critical sites + Exp 15 relationship
### §9.1 Primary fix sites (ONLY files edited; WALKER-only, `d2d9a3b` line numbers)
- `wpda_walker.rs:7092-7099` (per-branch skip, site 3 — PRIMARY un-suppress): the `&& !is_starving_self_projection_operand(...)` guard, behind `IFP_DISABLE`.
- `wpda_walker.rs:6960-6983` (pure-proj Drop, site 2) + `:6128-6147` (singleton-bucket, site 1) + `:9909-9924` (cohort-shell B12, site 5): same IFP-A guard.
- `wpda_walker.rs:7064-7071` (child descriptor insert, site 4) + `:2893-2945` (`ProjDescriptorKey`/`extract_proj_descriptor`): IFP-C.
- new fn `is_starving_self_projection_operand` (C1-C4) near `is_projection_fork:2759`; C4 reuses `single_hop_coercion:331`/`lossless_targets`.
### §9.2 Read-only authorities
`:14076-14346` (`allocate_fork_push_child` — `register()→WorkerInserted` `:14143`, CrossCatProjection push `:14325`); `:14990-15080` (`cursor_gss_pop_via_edge` — resolve gate `:15013`); `:14480-14560` (`revive_cohort_member_with_snapshot` — PROVEN-WRONG, MUST NOT route through; P3 proves it doesn't); `:315`/`:4843-4884`/gen `:21599` (`min_terminal_span`=C3); `:2759` (`is_projection_fork`), `:5859`/`:6599`/`:6869` (cycle/recovery — UNTOUCHED); `:4260-4324` (`resolve_at_end_of_input`/`accepting_indices` — the un-starved arm); `gss.rs` (`EdgeKind`=C1 key); `dispatch_cohort.rs:526`/`:581` (`register`/`resolve` — the worker/member dichotomy, UNCHANGED); `prefix.rs:1232` (`emit_cross_cat_prefix_unary_arm` — read-only unless R6); `calculator.rs:104`/`:128-129`/`:100-110` + `ast/language.rs:1048`/`:1066`/`:1110-1111` (lattice asymmetry C4 reads — NOT edited); `binder.rs:1035` (prefix-Fork — UNTOUCHED); `lex_weight.rs` (UNTOUCHED).
### §9.3 Exp 15 relationship (composes, no conflict)
`exp15-cps-trampolined-walker.md` is an orthogonal MEMORY/PERF rewrite (CPS/trampoline driver + persistent CursorStore); it explicitly preserves the grammar surface, SPPF, `WpdaStepAction`, the engine→walker contract, and the cross-cat/GLL/cohort-resolve semantics. **IFP is a parse-CORRECTNESS change (un-suppress a worker at the GLL gate); Exp 15 is a representation change (cost per cursor).** They COMPOSE: IFP changes WHICH cursors are produced (one more worker per starving cast-fold level); Exp 15 changes the COST per cursor. The IFP gate logic re-applies atop the CPS walker as a `Continuation`-enqueue guard. IFP is the narrow correctness-first down-payment proving the same-cat self-projection worker-ization is sound + bounded on the CURRENT walker, de-risking the rewrite. M0's flip-confirm bounds R6 to a 4-build check.

---
## Provenance
Designed by Plan agent `a70c05d4` (2026-06-02), grounded against `d2d9a3b` + the census artifacts (`fwdproj-recover-{int,float}-census.log`) + the 6th-attempt verdict + all 5 GLL gate sites + the `register/resolve` worker-vs-member dichotomy. THE breakthrough: the in-line continuation already exists — it is the `RegisterOutcome::WorkerInserted` cursor (live forward state), vs the `InflightCollision→revive_cohort_member_with_snapshot` path (stale). INT passes because its rich lattice worker-izes its projection at every level (incl. top-level `hi_pos=11` via distinct-cat Int→BigInt→Proc); Float fails because its sole same-cat ProcFloat self-projection is GLL-suppressed before it can become a worker. IFP = a precisely-triggered GLL un-suppression (4 structural clauses) + descriptor advance, worker-izing Float's self-projection exactly as INT's, recursively incl. pos-0, with M0 as the BLOCKING build-and-run flip-confirm. Supersedes the forward-REGISTRATION (`fwdproj-STOP-M0`, the 6th falsification); the narrow correctness-first down-payment on Exp 15.