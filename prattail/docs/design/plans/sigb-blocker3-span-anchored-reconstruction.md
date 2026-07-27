# Sig-B Blocker-3 — SPAN-ANCHORED OUTER-CAST RECONSTRUCTION (cast family's last 3 tests, M7.0–M7.4, 2026-06-01)

**pgmcp experiment #9.** FIFTH redesign. Supersedes the cohort-revival track (M5.0→M5.1→M6.0 EXHAUSTED) with a **deeper, evidence-driven root-cause re-localization** that overturns the M6.0 R1 STOP verdict.

Design-only (read + Explore + Bash-read-only; NO tree modification). Base = `6507b9c` + `/var/tmp/suite-green/sigb-cast-family-COMPLETE.patch` (Blocker-2). The M5.1 retention (`sigb-cast-family-M51-STOPPED.patch`) is REJECTED as a foundation (it is the over-fire mechanism this plan abandons); build on **Blocker-2 only** (§2.5 justifies). The committed HEAD `12234f9` is NOT Blocker-2 — Blocker-2 lives only in COMPLETE.patch; the implementer applies it in the worktree first (the working tree lacks `wrap_cat`/`take_pending_for_drain_crosswrap`; verified).

---

## §0. Residual (measured, against Blocker-2 = COMPLETE.patch)

Three tests ERR (calc 210/7 baseline; success = 213/4), all surface error `"1:N: expected no accepting branch reached end of input, found '<tok>'"`:

- **`simulator_regression_bool_prefix_tokens`** (`languages/tests/calculator.rs:2176`) on the two VAR-FIRST inputs in the corpus: `int(y != true > x < "qua")` (`:2188`) and `int(y and b == y < "x")` (`:2189`). Tokens for `:2188`: `0=int 1=( 2=y 3=!= 4=true 5=> 6=x 7=< 8="qua" 9=) 10=Eof`. The 6 boollit-first / paren-first inputs in the same corpus PASS.
- **`test_nested_float_float_int`** (`:1054`): `float(float(10, 64), 64)`. Tokens: `0=float 1=( 2=float 3=( 4=10 5=, 6=64 7=) 8=, 9=64 10=) 11=Eof`.
- **`test_triple_nested_float`** (`:1059`): `float(float(float(10, 64), 64), 64)` (one level deeper).

**The two families have DIFFERENT root mechanisms (PINNED in §1) — the M6.0 doc treated them as one and split the verdict the wrong way.** The Bool family's genuine body IS in the cohort cache (overturning M6.0 R1). The Float family's outer body is NEVER a cohort entry (a separate, deeper structure). The fix MUST address both, and they need DIFFERENT sub-mechanisms (§2).

---

## §1. Reconciled PHASE-1 mechanism — the M7.0 DIAGNOSTIC-CONFIRM spec

Every `[Cn]` predicate below is grounded in a named code site (Blocker-2 line) + a named M6.0 trace artifact already on disk (`/var/tmp/suite-green/b3-coerce-m60-*.stderr`). The implementer's M7.0 diagnostic MUST reproduce every `[Cn]` BEFORE any behavioral change. **STOP gates are marked.**

### 1.1 The forward-path liveness asymmetry (reconciles M5.0 with the boollit/var split) — code + trace confirmed

The genuine outer `int(`/`float(` cast resolves on the FORWARD path, never as a cohort `take_outer_cast_revival` member (the brief's M6.0 finding — CONFIRMED, NOT challenged). The question M5.0/M6.0 left open: **why does the forward outer-cast cursor survive-to-`!progress_made` for boollit-first but die via `Error("all fork branches dropped")` for var-first?**

The answer is **FIRST-set ambiguity at the body's first token**, code-confirmed at `first_set_of_category` / `collect_first_set` (`macros/src/gen/runtime/wpda_codegen/prefix.rs:457`/`:491`): every category's FIRST set contains `Ident` (the synthetic-Var contribution, `prefix.rs:546`).

- **boollit-first** (`int(true …)`): the body's first token `true` (BooleanLit) is UNIQUE to FIRST(Bool). The `int(` PrefixDispatch arm on `true` is a SINGLE Pass-2c `ImplicitCast` Push (`prefix.rs:1488` singleton arm) delegating to Bool via `CrossCatDelegate` — the live worker parses the body AS Bool and the `BoolToInt` cast fires on the Return-pop (`apply_pop_body_to_cursor:13593` → `emit_fire_action:11787`) over a category-correct child. The cursor survives. **Trace: `b3-coerce-m60-C61pass.stderr` exits `EXIT=fanout_!progress_made boundary … branch_cursors=13` — a LIVE outer frontier; `Int::parse → OK`.**
- **var-first** (`int(y …)`): the body's first token `y` (Ident) is in EVERY category's FIRST set. The `int(` PrefixDispatch arm on `Ident` is a **Fork over ~12 cross-cat delegations** (`emit_unified_arm`'s multi-descriptor branch, `prefix.rs:1535`), one per cast/projection whose source category admits `Ident`. Each Fork branch is a `CrossCatDelegate` that registers a DISTINCT-wrap cohort entry at `(pos=2, source=S, bp=0)` (M4 wrap-keying, `dispatch_cohort.rs:1076`). The genuine `BoolToInt` line is ONE fork among many, and its body resolution is governed by the cohort machinery — which is where it dies (§1.2).

`[C7-1]` (FIRST-ambiguity is the trigger): at the `int(` dispatch for `:2188`, the `Ident` arm emits a Fork with ≥2 `CrossCatDelegate` branches that register ≥2 distinct-wrap cohort entries at `(pos:2, *, bp:0)`, ≥1 returning `InflightCollision`. For the boollit-first input, the `true` arm emits a SINGLE Push (no Fork), 0 collisions at the body-start dispatch. Trace: the `REGISTER key={pos:2,…}` outcomes in `b3-coerce-m60-T1bool.stderr` (var-first) show both `WorkerInserted` and `InflightCollision` at `pos:2` across many wraps; the C61pass trace's body-start dispatch does not. **(Confirmed in evidence: `REGISTER key={pos:2,src:7,bp:0,wrap:(0,2)} … InflightCollision`.)**

### 1.2 The PRECISE death mechanism — clause-3 positional rigidity, NOT category mismatch (overturns M6.0 R1)

This is the central re-localization. Under M5.1 the outer cast member is revived by `take_outer_cast_revival` (`dispatch_cohort.rs:1697`, M5.1 patch), which pairs a paused member `K_sib` with a Resolved body `R` iff (clause 1) `K_sib != R`, (clause 2) `K_sib.equiv() == R.equiv()`, (clause 3) **`K_sib.pos == R.pos_at_dispatch`**, (clause 4′) `R` Resolved with `sib_hi == R.hi_pos`. The M6.0 doc concluded (R1) "NO category-correct full-span body exists in the cohort cache" → STOP. **This is FALSE, and the M6.0 diagnostic itself disproves it:**

- **The full-span Bool body DOES exist.** `b3-coerce-m60-T1bool.stderr`: `R key{pos:4,src:7,bp:0,wrap:(0,2)} sym=91 span=[Some(2),9] body_cat=Some(7) pos_at_dispatch=4`. **`sym=91` is a Bool-category (cat=7) Symbol spanning the FULL body `[2,9]`.** Its SPPF span lo = 2 (= the outer member's dispatch position); its cohort key `pos_at_dispatch = 4`.
- **The genuine outer cast member is at `pos=2`** (it dispatched its body right after `int(`): `REGISTER key={pos:2,src:7,bp:0,wrap:…}` and the M60 PAIR scan shows `K_sib{pos:2,…}` members.
- **Clause-3 forbids the pairing**: `K_sib.pos (=2) ≠ R.pos_at_dispatch (=4)`. So the `pos=2` member is paired ONLY with bodies whose `pos_at_dispatch=2` — and at pos 2 the only Resolved bodies span `[2,3]` (the bare var `y` and its wraps): `PAIR R{wrap:(7,38),sym=10,hi=3} … K_sib{pos:2,…}`. Every `pos=2` PAIR has `hi=3`. **The wall is positional, not categorical.**

**WHY does the full chain key at `pos_at_dispatch=4` and not `pos=2`?** Left-associative folding. `y != true > x < "qua"` parses as `(((y != true) > x) < "qua")`. The bare-var operand `y` resolves at the `pos=2` dispatch as `[2,3]`. The comparison operators (`!=` at pos 3, `>` at 5, `<` at 7) extend it through the InfixLoop/Pratt path. The cross-cat WRAP that produces the full-span Bool Symbol `sym=91` is registered when the chain's projection re-dispatches — at `pos_at_dispatch=4` (the dispatch of the RHS-bearing operand after the first `!=`), NOT at the outer `(`-dispatch pos 2. The SPPF span of `sym=91` is `[2,9]` (correct extent), but its cohort cache KEY carries the inner dispatch pos.

`[C7-2]` (THE central confirm — overturns M6.0 R1): at the var-first drop boundary, the cohort cache holds a Resolved `R` with **`R.symbol_id`'s SPPF span `[lo, hi]` where `lo == outer_member.pos (=2)` AND `hi == outer_full_span (=9)` AND `body_cat == BoolToInt's arg cat (Bool=7)`** — i.e. a category-correct full-span body keyed at `R.pos_at_dispatch ≠ outer_member.pos`. Read-only: re-run the M6.0 survey, AND additionally print `self.sppf.node(R.symbol_id)`'s `(lo_pos, hi_pos)` (the SPPF SPAN, `sppf.rs:169`) alongside `R.pos_at_dispatch` (the KEY pos). **If for the genuine Bool family there is NO Resolved body whose SPPF span lo == the outer member's pos AND hi == the outer full span AND body_cat == arg cat → the re-localization is wrong → STOP+report.** (Existence proof in hand: `sym=91 span=[Some(2),9] body_cat=Some(7)`.)

`[C7-3]` (clause-3 is the SOLE wall for the Bool family): for the Bool family, confirm that pairing the `pos=2` outer member with `sym=91` (the `[2,9]` Bool body) under a clause-3 RELAXED-to-span predicate (member.pos == R.span_lo, instead of member.pos == R.pos_at_dispatch) yields a `[C7-3a]` category-correct fire (the existing M6.0 `[C6-5]` transient-fire probe returns `Some` with `output_cat == Int`) AND `[C7-3b]` the resulting member pos == R.span_hi == 9 (so the next step consumes `)` at pos 9). Read-only: extend the M6.0 PAIR probe to ALSO scan span-anchored pairings (member.pos == R.span_lo). **If the span-anchored Bool pairing does NOT produce a fire-Some with pos-alignment → STOP.**

### 1.3 The Float family is STRUCTURALLY DIFFERENT — no outer cohort entry at all (a separate sub-mechanism)

For `float(float(10,64),64)` the outer cast `FloatBin . a:Proc, w:Int |- "float" "(" a "," w ")" : Float` (`calculator.rs:383`) is a **2-PARAM FOLD, NOT a unary cross-cat cast**. Its first slot `a:Proc` is the UNIVERSAL injection target, parsed via the HOME `Proc` PrefixDispatch (NOT a `<Y>To<X>` trigger-cast delegation). Consequently:

- **`b3-coerce-m60-T2float.stderr` at the drop boundary: `ALL_DROPPED at pos=1 … resolved_total=0 inflight_total=0 drained_pairs=0 outer_cast_revival_candidates=0`, `crosswrap_drained_pairs=0`, `SUMMARY eligible_pairs=0`.** The OUTER `[2,10]` body is NEVER a cohort `Resolved` entry. All cross-cat REGISTERs cluster at `pos:0/2/4/6` (the INNER `float(10,64)` region); pos 8/9/10 (the outer `, 64 )` tail) have ZERO cross-cat registrations.
- The inner `float(10,64)` resolves as **Float** (`body_cat=Some(6)` at inner spans). The outer `a:Proc` slot must hold `ProcFloat(inner_Float)` — `ProcFloat . f:Float |- f : Proc` (`calculator.rs:101`, a Pass-2a `CrossCatProjection`, `classify_atomic:227`). The Proc PrefixDispatch at pos 2 on `float(` DOES synthesize a `ProcFloat` projection delegating to Float-parsing. **The failure is that the inner FloatBin's Float result, after resolving `[2,7]`, does not get the `ProcFloat` wrap interposed so the outer `FloatBin`'s `a:Proc` slot is filled and the outer fold can fire over `[2,10]`.**

Contrast: `float(float(3))` (`:1291`) PASSES — both are UNARY casts (`IntToFloat`/`FloatId`), no 2-param `a:Proc` fold. The single-arg nested case works; the 2-arg `FloatBin` nesting fails. This isolates the defect to the **inner-cast-result → outer-`a:Proc`-slot projection across the `,` boundary in a nested 2-param fold**.

`[C7-4]` (Float family is a no-cohort-entry / Pratt-path projection gap): at the float drop boundary confirm (a) `outer_cast_revival_candidates == 0` and no Resolved entry has SPPF span `[2,10]` (outer) — the outer FloatBin is NOT a cohort member; (b) a Resolved/SPPF Float Symbol spanning the INNER `[2,7]` exists (`body_cat=Some(6)`); (c) `single_hop_coercion(Float=6, Proc=0)` returns the `ProcFloat` rule (non-empty). Read-only. **If (b) or (c) fails → the Float gap is even deeper → STOP+report for the Float family (the Bool family may still proceed independently — check the families SEPARATELY, as M6.0 mandated).**

`[C7-5]` (the inner Float reaches the outer slot via the live path once projected): construct the candidate `ProcFloat`-wrapped inner Float Symbol (the §2 splice for ONE inner-float→outer-Proc pairing) and fire the outer `FloatBin` action over `(ProcFloat(inner), 64)` via `fire_action_via_transient` (`:11660`); assert it returns `Some(_)` (output cat Float). **If it elides → STOP.**

### 1.4 Token-soundness invariant (unchanged backstop)

`min_terminal_span` (`wpda_walker.rs:257` default 0; codegen override emits per-rule: `BoolToInt`/`FloatBin`→1 trailing `")"`, `ProcFloat`/`ProcInt`→0 transparent) + the realize-time span filter (`realize_node_leave:4711`) reject any packing whose `slack = sym_span − Σ child spans < min_terminal_span`. The §2 splice MUST preserve this: it interposes only the grammar's declared coercion over a body whose SPPF span is genuine (already token-sound), and the outer cast's own `)` IS consumed (pos advances to R.span_hi which is the `)` position). `[C7-6]`: confirm `min_terminal_span` returns the expected per-rule counts and `pass2c_token_soundness_probe` (`calculator.rs:2220`) stays green.

### 1.5 Drop-cause classification

The mechanism is **(a) premature-drop-by-non-evidence**: a sound derivation EXISTS for both families (the Bool body `sym=91` proves `int(Bool-chain)` parses; the inner Float proves `float(ProcFloat(Float),64)` folds), but the genuine outer-cast cursor is dropped before EOI evidence rejects it — for the Bool family because clause-3 positional rigidity prevents the span-correct body from reaching the member; for the Float family because the inner-result→outer-`a:Proc` projection is never interposed on the Pratt path. STOPPING the drop until evidence rejects it (by SPAN-ANCHORED reconstruction) is the principled fix.

---

## §2. Solution-space exploration + recommended approach

### 2.0 The full space (six candidates considered)

| # | Approach | Verdict |
|---|----------|---------|
| A | **Forward-layer fix**: make var-first dispatch keep the genuine outer-cast cursor alive like boollit-first | Strong, but incomplete alone — see 2.1 |
| B | **(B)-class genuine-outer-frame reconstruction from SPPF** (fabricate a resumable cursor) | Rejected — see 2.2 |
| C | **Grammar-side restructuring** | Rejected — see 2.3 |
| D | **M5.1 cohort-revival splice** (equiv-blind) | EXHAUSTED (M6.0); 16251-blowup |
| E | **M6.1 coercion-aware splice** (clause-5 category-compat) | Mis-localized; fires fine but pairs `pos=2` member only with `[2,3]` bodies → still fails the Bool full span; does nothing for Float (0 cohort entries) |
| **F** | **SPAN-ANCHORED outer-cast reconstruction** (recommended) | **Best — see 2.4** |

### 2.1 Why Forward-layer (A) is the RIGHT LAYER but insufficient alone

A's instinct is correct and is the reason the recommendation (F) lives at the forward/revival boundary rather than post-mortem: the death is a forward dispatch/liveness defect (clause-3 rigidity + the Float projection gap), and fixing it there is the most GENERAL. But a PURE forward fix — "make the var-first Fork keep the genuine `BoolToInt` line alive to `!progress_made` like boollit-first" — founders on the cohort architecture: at pos 2 with an `Ident`, the engine CANNOT know which of the ~12 cross-cat delegations is the genuine one until the body resolves; pausing them as cohort members is the existing (sound, O(1)-merge) design. Forcing all 12 to run as independent live workers re-introduces the chain-blowup the cohort cache exists to prevent (the COQ-S0/EquivKey O(N²) defense) and would regress chain Welch. **F is the forward fix done RIGHT: it keeps the cohort pause, and at the revival boundary it pairs the paused member with the body by SPAN ALIGNMENT (the evidence the body belongs to this member) instead of by dispatch-pos equality.** This is a forward-path correctness fix to the revival predicate, not a post-mortem frame fabrication.

### 2.2 Why (B) SPPF-frame fabrication is REJECTED (and how F avoids its trap)

(B) = synthesize a fresh outer-cast GSS cursor from `R.symbol_id`'s SPPF subtree. Rejected for the reasons the M5.1 doc §2.0 gave AND a sharper one: `realize_root_to_terms` (`:4693`) yields TERMS not cursors; there is no faithful source for the cast's pre-`(` GSS frame. **F sidesteps this entirely**: it does NOT fabricate a frame. The genuine outer-cast member's `return_frame` IS a real walked cursor (it pushed `(` and paused as `CohortMember.return_frame`, `dispatch_cohort.rs:1313`) — `revive_cohort_member_with_snapshot` (`:13480`) already reconstructs a sound `)`-consuming cursor from it (this is the SAME entrypoint Blocker-2's drain + §3d backstop use, proven sound across 16 M4-fixes + sentinels). F changes ONLY which body Symbol is spliced into that real member, by span-anchoring the pairing.

### 2.3 Why Grammar-side restructuring (C) is REJECTED

Rewriting the casts/comparisons so the body surfaces at the member's dispatch pos would (i) change the surface grammar (user-facing) — out of scope and risks the entire op-suite; (ii) not generalize (every new cast would need the same surgery); (iii) violate the principle that the PARSER must handle the declared grammar, not the grammar bend to the parser. Rejected.

### 2.4 RECOMMENDED — (F) SPAN-ANCHORED OUTER-CAST RECONSTRUCTION

**Core principle:** the EVIDENCE that a Resolved body `R` is the body a paused outer-cast member `M` awaits is **SPAN ALIGNMENT** — `R`'s SPPF span `[lo, hi]` satisfies `lo == M.pos` (the body starts where M delegated) — NOT dispatch-key-pos equality (`M.pos == R.pos_at_dispatch`), which the left-assoc fold breaks. F replaces clause-3 with a span-anchored predicate, in TWO sub-mechanisms (Bool family + Float family), both at the forward/revival boundary, both behind the `B3_DISABLE` lever.

**2.4a — Bool family: span-anchored revival (replaces M5.1/M6.1's pos-equality pairing).**

A NEW EOI-time + pre-Error drain `take_span_anchored_outer_cast(&mut self) -> Vec<CrossWrapSpliceJob<W>>` on `DispatchCohortCache`, distinct from `take_pending_for_drain_crosswrap` (forward, UNCHANGED) and replacing M5.1's `take_outer_cast_revival`. Eligibility for pairing a paused member `K_sib` with a Resolved `R`:

1. `K_sib` has non-empty `pending_members` (a genuine paused outer-cast continuation). [unchanged]
2. `K_sib.equiv() == R.equiv()` — narrow EquivKey read (R5 preserved). [unchanged]
3. **`R.span_lo == K_sib.pos`** — **THE SPAN ANCHOR (replaces clause-3 `K_sib.pos == R.pos_at_dispatch`)**. Read `R.span_lo` from `self.sppf.node(R.symbol_id)`'s `lo_pos` (`sppf.rs:169`). This is the evidence the body `R` starts exactly where `K_sib` delegated. **The forward `take_pending_for_drain_crosswrap`'s clause-3 (`pos == pos_at_dispatch`) stays byte-identical** — this is a SEPARATE drain.
4. **category compatibility (the sound part of M6.1 clause-5)**: `body_cat = R.symbol_id`'s `category_src_idx`; `tgt_cat` = the member's cast arg category from `(K_sib.wrap_cat, K_sib.wrap_rule)`; accept iff `body_cat == tgt_cat` OR `single_hop_coercion(body_cat, tgt_cat)` is non-empty (the M6.0 codegen table, ALREADY CORRECT+COMPLETE per the brief — `b3-coerce-m60-DELTA.patch`). This PREVENTS the M5.1 16251-blowup (cuts equiv-blind wrong-category pairings) AND supplies the coercion to interpose (§2.4c).
5. take-once: `(K_sib, R.symbol_id) ∉ crosswrap_drained` (shared monotone set — §3).

The span anchor (clause 3) + category compat (clause 4) TOGETHER are far more selective than M5.1's equiv-only pairing — `[C7-2]` shows the genuine pairing is `K_sib{pos:2}` ↔ `sym=91{span:[2,9]}`, a SINGLE span-aligned category-correct body, not 406 equiv-blind groups. **This both closes the Bool family AND eliminates the over-fire** (the over-fire was the symptom of pairing by equiv alone; span+category anchoring is the cure).

**2.4b — the revival pushes the member's OWN dispatch pos (not the body's key pos).** `revive_cohort_member_with_snapshot` (`:13480`) already sets `cursor.pos = hi_pos` and re-pushes `CategoryEntry(source)` at `pos_at_dispatch`. For the span-anchored job, pass `pos_at_dispatch = K_sib.pos` (the member's own dispatch pos = R.span_lo) and `hi_pos = R.span_hi`. The body Symbol's span `[K_sib.pos, R.span_hi]` is exactly the member's body extent → the GSS re-push at `K_sib.pos`, the SPPF push of `R.symbol_id`, and `cursor.pos = R.span_hi` are all span-consistent. The member's next step fires `BoolToInt` over the spliced Bool child and consumes `)` at `R.span_hi`. (`[C7-3b]` proves pos-alignment.)

**2.4c — coercion interposition (REUSE the M6.0 mechanism, ONLY when `body_cat != tgt_cat`).** When clause-4 matched via a single-hop coercion (e.g. a Bool body for a member whose `tgt_cat` is reached by one projection), interpose the grammar's coercion Symbol before the cast fires, EXACTLY as the M6.1 §2.2b design specifies (intern_packing + intern_symbol at the SAME span + `fire_action_via_transient` store into `sppf_symbol_terms`, `:12045-12065`). When `body_cat == tgt_cat`, push the body directly (byte-identical to Blocker-2 splice). At MOST ONE coercion hop (the `single_hop_coercion` table is depth-1 by construction; ≥2-hop ⇒ reject in clause 4). This reuses the verified `single_hop_coercion` codegen (`b3-coerce-m60-DELTA.patch`, retained) — NOT new.

**2.4d — Float family: interpose `ProcFloat` at the inner-cast→outer-slot boundary on the FORWARD path.** The Float family has NO outer cohort entry (`[C7-4]`), so 2.4a does not apply. The inner `float(10,64)` resolves as Float `[2,7]`; the outer `FloatBin`'s `a:Proc` slot dispatches via the Proc PrefixDispatch's `ProcFloat` Pass-2a projection at pos 2. The defect: when the inner FloatBin (a 2-param fold producing Float) resolves and the `ProcFloat` projection's Return-pop fires, the projection must wrap the inner Float as `ProcFloat(Float)` to satisfy `a:Proc`. **Diagnostic-gated finding** (`[C7-4]`/`[C7-5]`): the inner Float Symbol IS produced; the `ProcFloat` projection IS synthesized; what fails is that the inner FloatBin's result reaches the `ProcFloat` delegate's body slot. Two candidate fixes, decided at M7.0 by `[C7-5]`:

- **(d-i) — if the inner Float IS a cohort `Resolved` entry** keyed at the Proc-projection's dispatch pos (span `[2,7]`, the inner): then the Float family ALSO closes via 2.4a span-anchoring — the outer `a:Proc` member (the `ProcFloat` projection, paused) pairs with the inner Float body by `R.span_lo == ProcFloat-member.pos` and `single_hop_coercion(Float, Proc) = ProcFloat`. This is the UNIFIED path — preferred if `[C7-4]`/`[C7-5]` confirm a Float cohort entry exists.
- **(d-ii) — if the inner Float is purely Pratt-resolved** (no cohort entry for the outer `a:Proc` projection): then the gap is in the Pass-2a `CrossCatProjection` Return-pop handling of a 2-param-fold inner result. The fix is forward: ensure the `ProcFloat` projection's `apply_pop_body_to_cursor` fires over the inner FloatBin's Float Symbol (the same `emit_fire_action` success arm). This is a narrower forward-dispatch fix, scoped at M7.0.

**The implementer MUST run `[C7-4]`/`[C7-5]` FIRST and pick d-i (unified) or d-ii (forward) per evidence. If neither holds (the inner Float never reaches the projection slot at all) → STOP for the Float family.**

### 2.5 Why F beats the alternatives (tractability / risk / generality / invariant-safety)

- **Generality (the decisive axis):** F fixes the REVIVAL PREDICATE (span-anchor instead of pos-equality) — a principled correctness fix that closes ALL casts whose body folds left-associatively past the member's dispatch pos, not a 3-test patch. M6.1's clause-5 alone would patch nothing (it pairs `pos=2` only with `[2,3]` bodies). The span anchor generalizes to any chain depth / any cross-cat cast.
- **Risk:** F REUSES the entire Blocker-2 + M6.0 verified machinery (`revive_cohort_member_with_snapshot`, `CrossWrapSpliceJob`, `single_hop_coercion`, `min_terminal_span`); the only NEW logic is the span-read (`sppf.node(R.symbol_id).lo_pos`) and the predicate swap. The forward per-step drain + §3d backstop + clause-4 are byte-identical → `cross_cat_with_parens` + sentinels protected by construction.
- **Tractability:** one new drain method + one walker call + (Float) one projection-fire fix. No GSS fabrication, no in-drain multi-step walk (the trap that killed prior designs 1/2).
- **Invariant-safety:** the span anchor is pure EVIDENCE (the body's span IS the proof it belongs to the member) — no weight/cost/threshold. Category compat REMOVES only provably-incompatible pairings (evidence). `Ambiguous` first-class (multiple span+category-aligned bodies → multiple revives through `merge_equivalent_cursors`, `:9621`). `K_sib` never removed.
- **Welch-neutral:** the new drain fires only at `branch_cursors.is_empty()` (pre-Error) and `!progress_made` (EOI), both reached only on cross-cat workloads with non-empty Resolved cohort entries; on cast-free chains the entries are empty → O(1) return-0 → byte-identical hot path.

**Build on Blocker-2, NOT M5.1.** M5.1's `take_outer_cast_revival` IS the equiv-blind over-fire mechanism F replaces; carrying it forward would require disabling it anyway. F's `take_span_anchored_outer_cast` is the principled successor. (If M7.0 reveals the span read needs the M5.1 retention scaffolding (`revive_outer_cast_members` walker wiring), the implementer MAY cherry-pick that thin wiring — but the ELIGIBILITY logic is F's, not M5.1's.)

---

## §3. Termination (the existing monotone take-once set is the certificate; no new cap)

`take_span_anchored_outer_cast` inserts each spliced `(K_sib, R.symbol_id)` into the SAME monotone non-shrinking `crosswrap_drained: FxHashSet<(DispatchKey, SppfId)>` (`dispatch_cohort.rs:458`, insert mirrors `:1479`, cleared ONLY at parse boundary `:506`), shared with the forward drain + §3d backstop, and SKIPS any present pair (clause 5). So each `(K_sib, R-body-symbol)` is span-revived AT MOST ONCE per parse. The span anchor + category compat only SHRINK the eligible set vs M5.1 (strictly fewer pairings — provably; `[C7-2]` shows a single genuine pairing vs M5.1's 406 groups). Therefore:

- retention-fires ≤ `|crosswrap_drained|` ≤ #DispatchKeys × #SPPF-symbols — grammar/input-bounded (members ≤ `MAX_PENDING_COHORT_PER_KEY = 16`, `dispatch_cohort.rs` cap).
- Each pre-Error retention (§2.4 site) that injects ≥1 cursor strictly grows `crosswrap_drained` (≥1 new pair). A retention finding no undrained span-aligned pair returns 0 → the Error path proceeds → that branch terminates.
- The interposed coercion Symbol is interned ONCE per `(body_symbol_id, coercion_rule)` via the SPPF `intern_symbol` dedup at `(nt, lo, hi)` — no unbounded SPPF growth (the span is the body's own span; no fresh extent).
- `max_steps` (`run_to_end_of_input:3974`, `Err(WpdaMaxStepsExceeded)`) is the hard backstop; disjoint from `MAX_REVIVAL_ROUNDS=4` (orphan path, `:8953`). M7.3 asserts retention-fires ≤ `crosswrap_drained.len()` AND `crosswrap_splices_total` ≤ the static product AND **STRICTLY LOWER than M5.1's 16251** (the span+category prune is measurable).

Float-family d-ii (forward projection fire) adds NO new drain — it fires inline on the existing Return-pop path, bounded by the existing forward termination (visited_proj_descriptors GLL cycle defense, `ProjDescriptorKey`).

---

## §4. Invariants preserved (every Blocker-2 gate holds)

- **WPDA end-to-end disambiguation; no premature drop-by-non-evidence.** §2.4 ADDS sound cursors (the body provably resolved = the Resolved `R` at the member's span); the span anchor + category compat REMOVE only provably-incompatible pairings (evidence: wrong span / no coercion). No weight/cost/threshold. `K_sib` never removed.
- **`Ambiguous` first-class.** Multiple span+category-aligned bodies → multiple spliced cursors; multiple bridging coercions → one job each. All flow through `merge_equivalent_cursors`/SPPF-dedup (`:9621`) on the re-entered step.
- **Forward clause-3/clause-4 UNCHANGED.** `take_pending_for_drain_crosswrap`'s clause-3 (`pos == pos_at_dispatch`, `dispatch_cohort.rs`) and clause-4 (`sib_hi < r_hi_pos`, `:1373`) are byte-identical → `cross_cat_with_parens` (`:2159`) STAYS GREEN (the parens-inner steal is excluded at every per-step level). The span-anchored eligibility is a SEPARATE EOI/pre-Error-only drain.
- **§3d backstop byte-identical** (`crosswrap_backstop_for_pausing_member`, `:1687`) — the boollit-first path (which works) is untouched.
- **EquivKey narrow, cache full DispatchKey (M4 67>23).** §2.4 reads `K_sib.equiv()` + `K_sib.wrap_cat/wrap_rule` + `R.span_lo` (all READ-only). Cache + `crosswrap_drained` + `cohort_origin` stay full `DispatchKey`.
- **Token-soundness backstop intact.** §2.4c interposes only depth-1 grammar coercions over genuine-span bodies; the outer cast's `)` IS consumed (pos → R.span_hi); `min_terminal_span` realize filter (`:4711`) is the EVIDENCE backstop. `pass2c_token_soundness_probe` + `wpds_parse_rejects_bare_bool_in_int_slot_token_unsound` MUST stay green.
- **Preserve the closed set.** Blocker-1 GLL descriptor (`ProjDescriptorKey`) + Blocker-2 splice + §3d backstop + M4 keying + C-bis Newton + 16 M4-fixes + 8/9 M4-regressions + nested + the 3 M3.1-sentinels (`cross_cat_dispatch_chaining` `:2119`, `cross_cat_with_floats` `:2272`, `test_nested_int_int` `:1064`) + `cross_cat_with_parens` + gauntlet 4220/0 + C-bis 0-fail + op-suites ≥1331/532 + soundness/`-3!`/parity + chain Welch WIN — all unaffected (forward path byte-identical; the new drain fires only when the forward path collapses on a cross-cat cast).
- **Welch-neutral on cast-free chains.** New drain reached only at `branch_cursors.is_empty()` / `!progress_made` AND guarded by non-empty Resolved entries (false on chains → O(1) return-0). Per-step hot path untouched.
- **`B3_DISABLE` A/B.** `B3_DISABLE=1` skips §2.4a + §2.4c + §2.4d entirely → EXACTLY Blocker-2's 8/9. Sole new lever. (NEW `B3_SPAN_DISABLE` optionally isolates the span anchor from the coercion interposition, for finer A/B.)

---

## §5. Milestones (ONE worktree `/var/tmp/wt-b3-span`; serial FOREGROUND `cargo`; **every build/test/bench wrapped in `systemd-run --user --scope -p MemoryMax=…` — 32G ceiling for full builds, 16G/8G per individual test/bench since the user runs concurrent work — NOT 96G; `--scope` runs SYNC, do NOT pass `--wait`; self-clean + verify `pgrep -x rustc`==0; main tree NEVER modified**). Base = `6507b9c` + `sigb-cast-family-COMPLETE.patch` applied in the worktree (verify `wrap_cat` + `take_pending_for_drain_crosswrap` present after apply). Reuse env gates `SIGB_CROSSWRAP`/`SIGB_TRACE`/`B2_DISABLE`/`B3_DISABLE`; NEW `B3_SPAN_DISABLE` (skips §2.4 span-anchored drain + coercion → falls back to EXACTLY Blocker-2's 8/9; the A/B lever).

- **M7.0 — DIAGNOSTIC-CONFIRM gate FIRST (INERT, READ-ONLY; like M5.0/M6.0).** Reuse the M6.0 machinery (the `SIGB_M60` survey + `[C6-5]` transient-fire probe in `b3-coerce-m60-DELTA.patch`). ADD to the survey, at the drop boundary: for each Resolved `R`, print `self.sppf.node(R.symbol_id)`'s `(lo_pos, hi_pos)` (the SPAN) alongside `R.pos_at_dispatch`; for the genuine outer member, print whether a span-anchored category-correct body exists (`R.span_lo == member.pos ∧ R.span_hi == outer_full_span ∧ cat_compat`). **GATE — all six `[C7-n]` reproduced:** `[C7-1]` FIRST-ambiguity Fork at the var-first body-start (≥2 collisions) vs single Push for boollit-first; **`[C7-2]` a category-correct full-span body keyed at a DIFFERENT dispatch pos EXISTS for the Bool family (`sym=91 span=[2,9] cat=7`)**; `[C7-3]` the span-anchored Bool pairing fires-Some + pos-aligns; `[C7-4]` the Float family has 0 outer cohort entries + an inner Float Symbol + `single_hop_coercion(Float,Proc)≠∅`; `[C7-5]` the `ProcFloat`-wrapped inner Float fires the outer FloatBin Some; `[C7-6]` `min_terminal_span` + `pass2c_token_soundness_probe` intact. **Mechanical:** gauntlet 4220/0; calc == Blocker-2 210/7; chain Welch NEUTRAL (all additions inert). **STOP gates: if `[C7-2]` falsified → the Bool re-localization is wrong (do NOT wire §2.4a). If `[C7-4]`/`[C7-5]` falsified → the Float family is a deeper gap (do NOT wire §2.4d; the Bool family MAY still proceed). Check the two families INDEPENDENTLY — the verdict may split.** Decide Float path d-i (unified span-anchor) vs d-ii (forward projection fire) here.

- **M7.1 — wire §2.4a span-anchored Bool revival + §2.4c coercion interposition (REUSE `single_hop_coercion`), gated `!b3_disabled() && !b3_span_disabled()`.** NEW `DispatchCohortCache::take_span_anchored_outer_cast` (span-read clause 3 + category clause 4, shares `crosswrap_drained`); walker `revive_span_anchored_outer_cast_members` calling `revive_cohort_member_with_snapshot` with `pos_at_dispatch = K_sib.pos`; pre-Error retention site at `step_fanout`'s `branch_cursors.is_empty()` (`wpda_walker.rs:9647`, Blocker-2) — attempt the drain BEFORE `Error("all fork branches dropped")`, re-enter the loop if ≥1 cursor injected. **GATE:** `bool_prefix_tokens` (incl. both var-first `:2188`/`:2189`) GREEN + the 3 M3.1-sentinels + `cross_cat_with_parens` + 16 M4-fixed + `parse_int_cross_cat_comparison_{ge,ne,lt,le}` + `_in_expression` + `test_nested_int_int` STAY GREEN + gauntlet 4220/0; `B3_DISABLE=1` restores EXACTLY Blocker-2's 8/9; `B3_SPAN_DISABLE=1` restores Blocker-2's 8/9. The splice count on the Bool target MUST be SMALL (span+category prune; assert ≪ M5.1's 16251). If any sentinel regresses OR the Bool target unmet → STOP+report.

- **M7.2 — wire §2.4d Float family (d-i unified span-anchor OR d-ii forward projection fire, per M7.0), gated.** **GATE:** `test_nested_float_float_int` (`:1054`) + `test_triple_nested_float` (`:1059`) GREEN + `test_nested_int_float` (`:1069`) + `test_nested_int_int` STAY GREEN + the Float-bearing `sin(3.14) + 3.0 * float(float(10,64),64)` (`:1075`) GREEN + `cross_cat_with_floats` (`:2272`) STAYS GREEN + gauntlet 4220/0. If d-i: same `take_span_anchored_outer_cast` closes it (preferred). If d-ii: the projection-fire fix must not regress any single-arg cast (`float(float(3))` `:1291`, `float(3)` `:1311`). `B3_DISABLE=1` restores 8/9. STOP+report on any regression.

- **M7.3 — TERMINATION + Welch + ambiguity.** TERMINATION test (`int(y != true > x < "qua")` + `int(y and b == y < "x")` + `float(float(float(10,64),64),64)` + synthetic 5-op/6-op var-first Int→Str-tail chains + synthetic quad-nested float — ALL parse AND RETURN; instrument + assert retention-fires ≤ `crosswrap_drained.len()` AND `crosswrap_splices_total` ≤ static product AND **splice-count ≪ M5.1's 16251 per input**) + interleaved Welch chain panel N≥51 (control `B2_DISABLE=1`; predict NEUTRAL/WIN) + chain_1000/2000 RSS +5% max + ambiguity-preservation probe (an input with two span+category-aligned bodies surfaces BOTH derivations).

- **M7.4 — full sweep.** gauntlet 4220/0; C-bis cycle/newton/tarjan/star/scc/self_loop 0-fail; op-suites `gen_calculator_op` ≥1331 / `gen_rholang_op` 532; soundness + `-3!` (edge_case 229/0 + probe_neg_zero 23/0) + parity 16/0 + cross_cat 2/0; `pass2c_token_soundness_probe` + `wpds_parse_rejects_bare_bool_in_int_slot_token_unsound` green; rholang pre-existing-fail ≤8. Save `git diff > /var/tmp/suite-green/sigb-cast-family-FINAL.patch` + a `b3-span-…` M7.k delta diff (pure additions).

---

## §6. GATES (= cast family FULLY closed) → merge `wip/cast-family-cohort` into `feature/wfst-architecture` + commit

calc release **213/4** (the 3 B3 targets GREEN; the 4 pre-existing eval-ambiguity remain) + ALL Blocker-2 gates hold: 5 Sig-B (incl. `bool_prefix_tokens`) + 4 realize-regressions + `cross_cat_with_parens` + 16 M4-fixed + the 3 M3.1-sentinels STAY GREEN + `test_nested_float_float_int` + `test_triple_nested_float` GREEN; gauntlet 4220/0; C-bis 0-fail; op-suites ≥1331/532; soundness + `-3!` + parity 16/0 + cross_cat 2/0; `pass2c_token_soundness_probe` green; Welch chain panel N≥51 no LOSS + chain RSS +5% max; ambiguity-preservation; TERMINATION (deep + synthetic-deeper return, bounded fires + splices, splice-count ≪ M5.1, no hang); `B3_DISABLE=1` restores EXACTLY Blocker-2's 8/9; `B3_SPAN_DISABLE=1` restores Blocker-2's 8/9. Zero regression.

---

## §7. Risks

- **R1 (PRIMARY) — `[C7-2]` falsified: the full-span category-correct Bool body is NOT in the cohort cache after all.** Mitigated by the existence proof ALREADY in hand (`b3-coerce-m60-T1bool.stderr`: `sym=91 span=[Some(2),9] body_cat=Some(7)`). M7.0 is INERT-FIRST; if the span read does not reproduce `sym=91`-shaped evidence, STOP. This OVERTURNS M6.0's R1 — the M6.0 diagnostic only checked SAME-pos pairings, so it never saw the cross-pos body. M7.0 must check span-anchored pairings explicitly.
- **R2 — Float family d-i/d-ii both falsified (`[C7-5]`).** The Float family is genuinely separate (0 outer cohort entries). If the inner Float never reaches the `ProcFloat` slot at all, the Float gap is deeper than a projection-fire. Mitigated: M7.0 checks the families INDEPENDENTLY; the Bool family closes regardless (split verdict allowed). If Float STOPs, report it as a distinct residual (the cast family closes for Bool; Float is a future 2-param-fold-projection plan).
- **R3 — span anchor over-fires (a body with `span_lo == member.pos` but wrong derivation).** Mitigated by clause-4 category compat + the realize-time `min_terminal_span` filter (a wrong-derivation body fires the cast but the yield≠span at realize → dropped on EVIDENCE) + `Ambiguous` keeping all sound alternatives. Gate: `pass2c_token_soundness_probe` + `cross_cat_with_parens` + sentinels green.
- **R4 — over-prune (category compat too tight) drops a genuine pair.** Clause-4 accepts `body_cat == tgt_cat` AND one-hop coercions; the all-var minimal `int(y != z > x < "qua")` MUST stay green (its body resolves Bool-compatible). Gate: all-var minimal + `B3_SPAN_DISABLE` A/B.
- **R5 — termination / splice blowup.** Span+category anchoring strictly SHRINKS the eligible set vs M5.1; monotone `crosswrap_drained` take-once certificate (§3); M7.3 asserts bounded fires + splice-count ≪ M5.1.
- **R6 — chain Welch/RSS regression.** New drain reached only at frontier-collapse / `!progress_made` + non-empty Resolved guard (false on chains, O(1)); per-step path byte-identical → NEUTRAL/WIN. Gate: Welch N≥51 control `B2_DISABLE=1`.
- **R7 — parens/sentinel regression.** Forward clause-3/clause-4 + §3d backstop UNCHANGED; span anchor confined to the EOI/pre-Error drain; `cross_cat_with_parens` + `_{ge,ne,lt,le}` + `_in_expression` + the 3 M3.1-sentinels gate; `B3_DISABLE=1` restores 8/9.
- **R8 — the span-spliced outer cast fires but the member's `return_frame` GSS can't consume `)` after the wrapped fire** (the deeper R7-of-R7). Mitigated: `[C7-3b]` proves pos-alignment (member.pos → R.span_hi = the `)` position) and `[C7-5]` proves the fire Some in isolation; M7.1/M7.2 surface any residual. If the target stays unmet after `[C7-3]`/`[C7-5]` passed, STOP (the member's continuation is structurally insufficient — a different splice-shape).
- **R9 — EquivKey leak.** §2.4 reads `equiv()` + `wrap_cat/wrap_rule` + `R.span_lo` READ-only; cache + `crosswrap_drained` full DispatchKey; 67>23 re-asserted.

---

## §8. Critical sites (Blocker-2 line numbers = `6507b9c` + COMPLETE.patch applied; the working tree is at BASE — apply COMPLETE.patch in the worktree FIRST)

- `prattail/src/dispatch_cohort.rs`:
  - `DispatchKey` (+ `wrap_cat`/`wrap_rule`, COMPLETE.patch widens `:63`/`new` 5-arg); `equiv()` (drops wrap, narrow EquivKey); `EquivKey`.
  - `take_pending_for_drain_crosswrap` (clause-3 `pos == pos_at_dispatch`, clause-4 `sib_hi < r_hi_pos` ≈ patch `:1373`) — **UNCHANGED, byte-identical** (forward, per-step).
  - `crosswrap_backstop_for_pausing_member` (patch `:1687`) — **UNCHANGED** (§3d, the boollit path).
  - `crosswrap_drained` (patch `:458`) / `crosswrap_splices_total` (`:463`) / clear (`:506`); `MAX_PENDING_COHORT_PER_KEY`; `CrossWrapSpliceJob` (patch `:1135`) — **REUSE**; `materialize_branch_cursor` — REUSE.
  - **NEW `take_span_anchored_outer_cast` next to `take_pending_for_drain_crosswrap` (~`:1500`)** — span-read clause-3 (`sppf.node(R.symbol_id).lo_pos == K_sib.pos`) + category clause-4 (`single_hop_coercion`) + take-once; the §2.4a/§2.4c core. (REPLACES M5.1's `take_outer_cast_revival`.)
- `prattail/src/wpda_walker.rs`:
  - `step_fanout` `:8936`; per-cursor `CursorOutcome::Drop` discard `:9467`; cohort drain block `:9499`; per-step cross-wrap drain call (COMPLETE.patch `:3643-3661`); `self.branch_cursors = new_cursors` `:9589`; **drop site `branch_cursors.is_empty()` → `Error("all fork branches dropped")` `:9647-9654` (INSERT §2.4 pre-Error span-anchored retention HERE).**
  - `run_to_end_of_input` `:3786`; `!progress_made` block (COMPLETE.patch adds `revive_orphaned_cohort_members_once` at `:4082`) — INSERT the EOI span-anchored retention alongside; top-of-loop `is_terminal()` `:3981`.
  - `revive_cohort_member_with_snapshot` `:13480` (REUSE; pass `pos_at_dispatch = K_sib.pos = R.span_lo`, `hi_pos = R.span_hi`; raw-body push `:13517`; **interpose coercion Symbol here when `body_cat != tgt_cat`, §2.4c**).
  - `apply_pop_body_to_cursor` `:13593` (cast fire `emit_fire_action` `:13698`) — UNCHANGED for Bool; **Float d-ii fix site (the `ProcFloat` projection Return-pop fire)**.
  - `emit_fire_action` `:11787` (success arm intern_packing `:12045` + intern_symbol `:12050` + `sppf_symbol_terms.insert` `:12065` — the shape §2.4c reuses; elide site `:12001-12019`).
  - `fire_action_via_transient` `:11660` (REUSE for `[C7-5]` probe + coercion fire); `reconstruct_action_arg` (reads `sppf_symbol_terms`); `is_accepting_config` `:5456`; `is_cursor_accepting_terminal`; `min_terminal_span` `:257` + `realize_node_leave` `:4711` (token-soundness backstop, UNCHANGED).
  - `allocate_fork_push_child` `:13245` (register `:13282`/`:13299`, wrap-keyed; `RegisterOutcome` match `:13303`; §3d backstop call COMPLETE.patch `:3919-3951`) — UNCHANGED; gates `b2_crosswrap_disabled` + NEW `b3_span_disabled`.
  - `ProjDescriptorKey` / `extract_proj_descriptor` (COMPLETE.patch `:2400`/`:2435`, the Blocker-1 GLL `w`-discriminator) — UNCHANGED.
- `macros/src/gen/runtime/wpda_codegen/`:
  - `semantic_actions.rs::emit_single_hop_coercion_body` + `engine_impl.rs:1808` `single_hop_coercion` impl (`b3-coerce-m60-DELTA.patch`, ALREADY CORRECT+COMPLETE — RETAIN; the §2.4c coercion table).
  - `prefix.rs:457` `first_set_of_category` / `:491` `collect_first_set` (the FIRST-ambiguity source, `:546` synthetic-Var Ident) — diagnostic reference, UNCHANGED.
  - `prefix.rs:1120-1194` Pass-2c `ImplicitCast` / `:1085-1118` Pass-2a `CrossCatProjection` / `:1488` singleton + `:1602` multi emission arms; `classify_atomic:203` (`CrossCatProjection` arm `:227` for `ProcFloat`) — diagnostic reference, UNCHANGED.
- `prattail/src/sppf.rs`: `SppfNode::Symbol{ category_src_idx, lo_pos, hi_pos }` `:169` (**read `R.span_lo`/`R.span_hi` for the span anchor — THE new read**); `intern_packing`/`intern_symbol`/`link_packing_to_symbol`/`node` (REUSE §2.4c).
- `languages/src/calculator.rs`: `BoolToInt:234` / `IntToBool:239` / comparison Bool rules `:144-173`; `FloatBin:383` (`a:Proc, w:Int` 2-param fold) + siblings `IntBin:377`/`FixedBin:386`; transparent projections `ProcFloat:101`/`ProcInt:100`; categories declaration order `:11` (Proc=0, Int=1, …, Float=6, Bool=7, Str=8).
- `languages/tests/calculator.rs`: `bool_prefix_tokens:2176` (var-first residuals `:2188`/`:2189`); `cross_cat_with_parens:2159`; `cross_cat_dispatch_chaining:2119`; `cross_cat_with_floats:2272`; `test_nested_float_float_int:1054`/`test_triple_nested_float:1059`/`test_nested_int_int:1064`/`test_nested_int_float:1069`; Float-bearing `:1075`; single-arg controls `float(float(3)):1291`/`float(3):1311`; `pass2c_token_soundness_probe:2220`; NEW TERMINATION test.
- Evidence artifacts (READ-ONLY, on disk): `/var/tmp/suite-green/b3-coerce-m60-T1bool.stderr` (Bool `sym=91 span=[2,9]` proof + `SUMMARY eligible_pairs=109 c6_5_fire_ok=99`), `b3-coerce-m60-T2float.stderr` (Float `eligible_pairs=0`, 0 outer cohort entries), `b3-coerce-m60-C61pass.stderr` (boollit-first `EXIT=fanout_!progress_made branch_cursors=13` live-survival contrast), `b3-coerce-m60-DELTA.patch` (the `single_hop_coercion` codegen, RETAIN).
