# Float-Prefix 2-Param-Fold Disambiguation — Closing the Cast Family's Last 2 Tests

**pgmcp experiment #9 (continuation) · 2026-06-01 · DESIGN ONLY**
Targets: `test_nested_float_float_int` (`languages/tests/calculator.rs:1054`, `float(float(10,64),64)`) and `test_triple_nested_float` (`:1059`, `float(float(float(10,64),64),64)`).
Base: `6507b9c` + `/var/tmp/suite-green/sigb-cast-family-FINAL.patch` ≡ tag `sigb-b3-span-FINAL` → `d2d9a3b` (Bool-closed cast family).

---

## §0 Residual statement and scope

The cast family is split-closed on the base: the **Bool subset is CLOSED** via M7.1 span-anchored revival (`:2188` `int(y != true > x < "qua")` parses); the **Float subset is STOPPED** — exactly two tests remain red:
- `float(float(10,64),64)` → `10.0`
- `float(float(float(10,64),64),64)` → `10.0`

The M7.2 STOP verdict established (and I re-confirm) that span-anchored reconstruction (`take_span_anchored_outer_cast`) does NOT close these — a full SPPF-arena scan finds **no Float Symbol** spanning the inner `[2,7]` or the outer `[2,10]`; the only Float Symbols are the atomic literals `[4,5]`(=10) and `[6,7]`(=64). This plan designs the DISTINCT principled fix, grounded in a mechanism pinned with live `PRATTAIL_TRACE` evidence on the base grammar.

**Out of scope / must not regress:** the Bool win (`:2188`), the M7.1/M7.3 span-anchored machinery, the 16 M4-fixes, 8/9 M4-regressions, the 3 M3.1 sentinels (`cross_cat_dispatch_chaining`, `cross_cat_with_floats`, `test_nested_int_int`), `cross_cat_with_parens`, gauntlet 4220/0, calc 214/6→target 216/4, C-bis, op-suites ≥1331/532, soundness/`-3!`/parity, chain Welch wins.

---

## §1 Verified PHASE-1 mechanism (confirm + deepen — the spec the fix must satisfy)

### 1.1 The localization was right but the *named* discriminator is FALSIFIED — and that matters

The M7.2 STOP localized the defect to "`float(` is the shared prefix of unary casts AND the binary `FloatBin` fold; the `float(`-prefix Fork doesn't resolve when the first slot is itself a cast." I **confirm the locus** but **falsify the implied discriminators**, which reshapes the fix:

- **Rule-count is NOT the discriminator.** From the DSL (`languages/src/calculator.rs`), `float(` and `int(` are *symmetric*: each has exactly **4 unary casts + 1 binary fold**.
  - `float(`: `IntToFloat`(`:230`,a:Int), `BoolToFloat`(`:231`,a:Bool), `StrToFloat`(`:232`,a:Str), `FloatId`(`:243`,a:Float) + `FloatBin`(`:383`,a:Proc,w:Int).
  - `int(`: `FloatToInt`(`:233`), `BoolToInt`(`:234`), `StrToInt`(`:235`), `IntId`(`:242`) + `IntBin`(`:377`).
- **The compile-time ambiguity is fully symmetric** across `int`/`float`/`bool`/`str`. The codegen emits the identical diagnostic for each (captured live, base build):
  > `Float: unresolvable ambiguity at [KwFloat, LParen] between IntToFloat and BoolToFloat and StrToFloat and FloatId and FloatBin — no finite lookahead can disambiguate`
  > `Int: unresolvable ambiguity at [KwInt, LParen] between FloatToInt and BoolToInt and StrToInt and IntId and IntBin …`
- **The generated walker arms are structurally identical.** `target/generated/calculator/wpda.rs`: the `float`-keyword fold-entry Fork (e.g. cat 5, line 1443) and the `int`-keyword fold-entry Fork (cat 2, line 1547) are the same shape — `Fork{ 5 branches → BinderRule{rule_idx∈{casts,fold}}, consume_trigger:true }`. `classify_binder` produces an identical `BinderShape` for `FloatBin` and `IntBin` (both `[Literal,Literal("("),Simple{Proc},Literal(","),Simple{Int},Literal(")")]`).

**Conclusion: `float(` is not special at the grammar or codegen layer. The defect is general; the `int`/`uint`/`fixed` cases only *appear* fixed because a downstream RECOVERY mechanism (Blocker-2 revival) rescues them, and that mechanism happens to fail for `float`.**

### 1.2 What actually happens — live-trace ground truth (base build, `PRATTAIL_TRACE`)

Three traces, same grammar, decisive:

| Input | Forward fanout behavior | Outcome |
|---|---|---|
| `float(10,64)` (standalone, `test_float_of_int`) | 5-way `[KwFloat,LParen]` fanout → blows to 40+ cursors → **converges**; a cursor reaches `node==GSS_NODE_NONE` (`4294967295` in trace at step 28) | **PASS** |
| `float(float(10,64),64)` (target) | identical 5-way fanout → 40+ cursors → collapses to a single `[94]` at step 47 → **step 48 `Error{"all fork branches dropped"}`** | **FAIL** |
| `int(int(5,32),32)` (analog) | **byte-identical** failing tail to the float target (steps 43–48 match exactly) | **FAIL on HEAD-forward; PASS on base via revival** |

Critical sub-findings:
1. **The forward parse cannot resolve ANY nested 2-param fold** — `int` and `float` fail forward identically. The forward `[Kw,LParen]` Fork is genuinely undecidable by lookahead; it fanouts and every branch retires non-accepting.
2. **Zero `on_cursor_dropped` callbacks fire** during the nested-float parse, yet it ends in `Error`. The branches retire *inside* `step_fanout` (non-accepting terminal states filtered by `cursor_resolution_check`), reaching `branch_cursors.is_empty()` (`wpda_walker.rs:10421`) → `Error`. This is precisely the M7.0 retention site.
3. **The parse TERMINATES** (errors at step 48, ~0.55 s) — no hang, no beam-prune. `MAX_STEPS` is not implicated.

### 1.3 Why `int` is rescued on the base but `float` is not — the true defect

On the base (`d2d9a3b`), `int(int(...))` passes **not by forward parse** but via the M1 / Blocker-2 recovery at `run_to_end_of_input`'s `!progress_made` hook (`wpda_walker.rs:4143`→`4157` `revive_orphaned_cohort_members_once`, and `:4170` `revive_span_anchored_outer_cast_members`). `revive_orphaned_cohort_members_once` (`:9049`) explicitly names `float(x)`/`int(a > b == c)` as cases that "NEED revival to surface a term-bearing / promoted-category derivation." Both revival paths require the inner cast to have left **a drainable artifact**:
- `revive_orphaned_cohort_members_once` drains `drain_orphaned_inflight_members()` — orphaned **InFlight cohort members** (`dispatch_cohort.rs:443-449`).
- `take_span_anchored_outer_cast` (`dispatch_cohort.rs:1058`) Pass 1 collects **Resolved bodies `R`** with a live worker and an SPPF span; Pass 2 span-anchors paused members to them (clause-3 `R.span_lo == K_sib.pos`, clause-4 `body_cat==tgt_cat ∨ single_hop_coercion≠∅`).

**For float, Pass 1 collects ZERO bodies** (M7.2 scan: no inner Float Symbol exists). So the question reduces to: *why does the inner `FloatBin` never become a Resolved SPPF Symbol, when the inner `IntBin` does?*

### 1.4 The precise upstream defect: SPPF Symbol-dedup `(nt, lo, hi)` collapse on the Float projection chain

The SPPF interns one Symbol per `(non_terminal_tag, lo_pos, hi_pos)` triple — this *is* the ambiguity-collapse mechanism (`sppf.rs:164-172`). The codegen already documents and fixes one instance of pathological collapse: a **unary-prefix** rule whose Symbol "shares `(nt, lo, hi)` with its sole operand → SPPF Symbol-dedup collapses both packings" (`sppf.rs:283-284`), repaired by giving the trigger a distinct `lo_pos` via `ConsumeAsTriggerOnly`/`TriggerTerminal` (`wpda_runtime.rs` `TriggerMode`).

The 2-param **function-call-form fold** `float(a,w)` does **not** get this protection: its `float` and `(` tokens are consumed as `TriggerMode::Discard` (generated arms at `wpda.rs:1443`, `consume_trigger:true` → discard), so the interned `FloatBin` Symbol takes `lo_pos` = its operand region. In `float(float(10,64),64)` the competing Float-category derivations over the inner region collide on `(Float_tag, lo, hi)`:
- the inner `FloatBin` reading (`float(10,64):Float`),
- the `ProcFloat`/projection wrapper needed to satisfy the outer fold's `a:Proc` slot (`single_hop_coercion(Float=6,Proc=0)=(0,8)=ProcFloat`, M7.2 `[C7-4](c)`),
- the unary `FloatId` mis-reading over an overlapping span.

These collapse, and the packing that survives dedup is not the one that lets the outer `FloatBin` reduce — so the inner Float Symbol that revival would need is **never retained as a Resolved body**. The `int` chain avoids the fatal collapse because its inner result is an `Int` Symbol whose realize span/slack (`min_terminal_span` + the `slack < min_span` filter at `wpda_walker.rs:5108-5135`) keeps a distinct, drainable InFlight orphan that `revive_orphaned_cohort_members_once` re-drives to a winning derivation. (The `min_terminal_span` default is `0`; the per-language body `emit_min_terminal_span_body` is the lever — see §2.)

**Spec the fix must satisfy:** make the inner `FloatBin` derivation *survive as a distinct, realizable SPPF Symbol / drainable cohort artifact* over its true span, so that (a) the forward fanout can converge OR (b) the existing revival can drain it — WITHOUT collapsing it against the projection/unary competitors, and WITHOUT narrowing the Fork alternative set.

---

## §2 Solution space + recommended fix

### Option A (REJECTED) — extend `take_span_anchored_outer_cast` to synthesize a Float body
Fabricate the missing inner Float Symbol so span-anchoring can fire. **Rejected:** there is no body to anchor (M7.2); synthesizing one is "inventing a derivation," violating the HARD INVARIANT (evidence-only). It also re-treads the STOP the base already recorded.

### Option B (REJECTED) — weight/threshold the `[KwFloat,LParen]` Fork toward `FloatBin`
Bias the 5-way Fork so the fold branch wins when a `,` is downstream. **Rejected:** this is premature disambiguation by weight; it would mis-resolve the legitimately-ambiguous unary `float(float(3))` cases and breaks "never narrow the alternative set to force acceptance."

### Option C (REJECTED) — grammar left-factoring of the cast keyword
Restructure `float(`-rules into a shared-prefix sub-category (per `left-factoring.md`). **Rejected for this plan:** it changes the DSL/grammar surface for every shipped language, is far beyond a 2-test fix, and risks the chain Welch / op-suite invariants broadly. Worth a separate epic, not this residual.

### Option D — RECOMMENDED: distinguish the fold Symbol's `lo_pos` so the inner fold survives dedup, restoring forward convergence (and, as backstop, drainability)

**The fix mirrors the already-proven unary-prefix `TriggerTerminal` repair, generalized to the function-call-form 2-param fold.** Concretely, the keyword-triggered fold (`KwFloat`/`KwInt`/… with a `(`-delimited multi-arg body) must intern its result Symbol with a `lo_pos` anchored at the **trigger keyword position**, not at the operand's `lo`. This makes the inner `FloatBin` Symbol `(Float_tag, trigger_pos, hi)` **distinct** from the operand/projection/unary Symbols over `(Float_tag, operand_lo, hi)`, so dedup no longer collapses the fold's packing.

Mechanism, building on existing machinery (no new disambiguation policy):
1. **Codegen — emit a distinguishing trigger position for fold rules.** In `macros/src/gen/runtime/wpda_codegen/binder.rs` (fold/keyword-prefix dispatch entry, the `emit_*prefix*`/`BinderRule` entry around `:1015-1190`) and `prefix.rs`, the fold's leading keyword is currently consumed `Discard`. Change the fold-rule entry to mirror the unary-prefix path: consume the keyword as a position-bearing trigger so the interned Symbol receives `lo_pos = trigger_pos`. The exact existing hook is the `TriggerMode`/`emit_push_trigger_terminal` path (`wpda_runtime.rs` doc at `min_terminal_span`'s neighbor) and the `with_kind_return`/`rule_at(...,slot,...)` Symbol construction. This is a *representational* change (the Symbol's span anchor), not a Fork-set change — all 5 branches still fire; only their interned spans become non-colliding.
2. **Realize slack filter stays sound.** With a trigger-anchored `lo_pos`, the fold Symbol's span is `[trigger_pos, hi]`, strictly wider than its operand sub-span, so `slack = sym_span − Σ child_span ≥ trigger_terminal_width`. The `slack < min_span` reject (`wpda_walker.rs:5135`) then *correctly* admits the genuine fold and still rejects token-unsound fabrications. If needed, set `emit_min_terminal_span_body` for the fold rules to `1` (one trigger terminal) so the slack accounting is exact — this is the same accounting already used for `BoolToInt(1,11)=1`.
3. **Forward convergence is restored by evidence.** With the inner `FloatBin` Symbol no longer dedup-collapsed, the outer fold's `a:Proc` slot can wrap it (via the existing `ProcFloat` projection), the outer `FloatBin` reduces, and a cursor reaches an accepting config exactly as the standalone `float(10,64)` already does. The fanout *resolves* rather than being force-pruned.
4. **Revival as backstop, unchanged.** If any residual ordering still parks the inner fold as an InFlight orphan, the inner `FloatBin` now leaves a **distinct drainable Symbol/cohort body**, so the *existing* `revive_orphaned_cohort_members_once` / `take_span_anchored_outer_cast` paths (clause-4 with `single_hop_coercion(Float,Proc)=(0,9 ProcFloat)`) can drain it with no new policy. No new revival code is required for the happy path; the backstop reuses M7.1 verbatim.

**Why D beats the alternatives:** it is the *same* principled repair the codebase already applied to unary-prefix Symbol collapse (`sppf.rs:283-284`), simply not yet extended to the function-call fold shape. It is evidence-preserving (Fork set untouched, `Ambiguous` first-class), Welch-neutral on cast-free chains (chains contain no `(`-delimited cast fold, so the changed arm is never reached — the same R4 argument the base's `b2_chain_bench` makes), and symmetric (it fixes `int`/`uint`/`fixed`/`bool`/`str` folds the same way, so it cannot create a new int/float asymmetry). It addresses the *upstream* dedup collapse identified in §1.4, not a downstream symptom.

**Token-soundness:** preserved and strengthened. The trigger-anchored `lo_pos` is the documented soundness device (`wpda_runtime.rs` TriggerTerminal note: it "prevent[s] the SPPF Symbol-dedup collision that otherwise silently drops the wrapping rule's derivation at realize time"). `min_terminal_span`'s slack filter remains the authoritative token-soundness backstop.

---

## §3 Termination argument

1. **No new unbounded loop.** D adds no iteration; it changes the `lo_pos` of an interned Symbol and (optionally) one `min_terminal_span` table entry. The fanout loop and revival loops are unchanged.
2. **Revival budget intact.** If the backstop fires, it reuses `revive_orphaned_cohort_members_once` (bounded by `MAX_REVIVAL_ROUNDS`, with the `SPURIOUS_ORPHAN_THRESHOLD=256` gate, `wpda_walker.rs:9049+`) and `revive_span_anchored_outer_cast_members` (take-once via the shared `crosswrap_drained` set, `dispatch_cohort.rs:1058+`). Both already carry termination certificates (M7.3 `sigb_b3_span_anchored_termination_bool`).
3. **Dedup still terminates realize.** Symbol dedup remains finite: distinguishing `lo_pos` can only *increase* the number of distinct `(nt,lo,hi)` keys by a constant per fold nesting level (one trigger position per fold), bounded by token count. The C-bis cycle handling (Tarjan/Newton, `wpda_walker.rs:4851+` gray-child skip) is unaffected.
4. **Empirical bound.** The target parses already terminate in <1 s pre-fix (they error); post-fix they must reach an accepting config in comparable steps (the standalone `float(10,64)` converges by ~step 30). The triple-nested test bounds the recursion depth probe.

---

## §4 Invariants carried

- **WPDA end-to-end disambiguation:** D restores convergence by making a genuine derivation *survive dedup*; it never narrows the cursor/alternative set, never weights/thresholds the Fork. `Ambiguous` stays first-class (legit ambiguous casts like `float(float(3))` still surface both readings).
- **Token-soundness via `min_terminal_span`:** preserved; the trigger-anchored span makes the slack filter exact for folds. A/B-checkable.
- **Welch-neutral on cast-free chains:** the modified arm is the `(`-delimited cast-fold entry, unreachable by chain workloads — same R4 guard as `languages/examples/b2_chain_bench.rs`. Full N≥51 panel required at the perf gate.
- **A/B disable lever:** gate the fold `lo_pos` change behind an env lever (e.g. `B3_FOLD_TRIGGER_DISABLE`, parallel to `b3_span_disabled()` at `wpda_walker.rs:113`) so the diagnostic-confirm and regression bisection can toggle it; unset → fix active.
- **Preserve everything closed:** Bool win, M4-fixes/regressions, M3.1 sentinels, gauntlet 4220/0, op-suites ≥1331/532, soundness/`-3!`/parity, C-bis.

---

## §5 Milestones (ONE worktree; serial FOREGROUND builds, each wrapped in `systemd-run --user --scope -p MemoryMax=32G`; 16G/8G per test; self-clean; multi-session OK)

**Setup (implementer):** create worktree off `6507b9c`, apply `/var/tmp/suite-green/sigb-cast-family-FINAL.patch`. **Verify base:** `int(y != true > x < "qua")` PARSES; calc **214/6**; gauntlet **4220/0**.

**M*.0 — DIAGNOSTIC-CONFIRM gate (INERT; STOP if falsified).** Reproduce §1.4 *before any behavioral change*:
- (a) Add an INERT, env-gated (`SIGB_FOLD_DEDUP`) diagnostic at SPPF intern of fold Symbols that logs `(nt, lo_pos, hi_pos)` for the `FloatBin`/`IntBin` interns on `float(float(10,64),64)` and `int(int(5,32),32)`. **Confirm:** the inner `FloatBin` Symbol's `(Float,lo,hi)` COLLIDES with a `ProcFloat`/`FloatId` Symbol over the same span (dedup hit drops the fold packing), whereas the inner `IntBin` does not lose its drainable artifact. **STOP if the collision is not observed** (mechanism falsified → re-localize).
- (b) Confirm via `PRATTAIL_TRACE=steps` that the float target fanout collapses to `branch_cursors.is_empty()`→`Error` (already captured) and that `take_span_anchored_outer_cast` returns 0 pairings for float (re-run the M7.2 SPPF scan). **Mechanical gate:** byte-identical calc 214/6, gauntlet 4220/0, chain Welch structurally neutral (diagnostic gated off).

**M*.1 — Codegen: trigger-anchored `lo_pos` for keyword folds (gated `!B3_FOLD_TRIGGER_DISABLE`).** Implement §2-D step 1 in `binder.rs`/`prefix.rs` + `wpda_runtime.rs` `TriggerMode` wiring; set `emit_min_terminal_span_body` for fold rules if slack accounting requires (step 2). **GATE:**
- `float(float(10,64),64)` → `10.0` and `float(float(float(10,64),64),64)` → `10.0` GREEN.
- All §0 protected items GREEN: Bool `:2188`, 3 M3.1 sentinels (incl. `test_nested_int_int`), `test_nested_int_float`, `cross_cat_with_parens/strings/floats`, the 4 `parse_int_cross_cat_comparison_*`.
- `B3_FOLD_TRIGGER_DISABLE=1` ⇒ both Float targets ERR (restores base); unset ⇒ GREEN. `B3_SPAN_DISABLE=1` still yields Bool behavior unchanged.
- calc **216/4** (214 + 2 Float; remaining 4 = pre-existing eval-ambiguity), gauntlet **4220/0**.

**M*.2 — Full sweep + Welch + soundness.** op-suites ≥1331/532; `-3!` ladder + `wpda_parity_*`; soundness/parity; C-bis; **chain Welch N≥51 (p<0.05, quiet) Welch-neutral**; the M7.3 termination/ambiguity-preservation tests still pass; add a Float-family termination test mirroring `sigb_b3_span_anchored_termination_bool` and an ambiguity-preservation test asserting `float(float(3))` (unary-in-unary) still resolves. Final SPLIT→**UNIFIED** verdict (Bool + Float both CLOSED). Save FINAL patch + delta; commit + tag.

---

## §6 Gates (every milestone)

- gauntlet `-p mettail-prattail --lib` → **4220/0**.
- calc full suite → **216/4** at M*.1+ (214/6 at M*.0).
- op-suites: `gen_calculator_op` **≥1331**, `gen_rhocalc_op` **532/0**.
- disambiguation gate: `-3!` ladder + `wpda_parity_calculator`.
- Welch (chain bench, N≥51, p<0.05, quiet) for the perf invariant — **only at M*.2** (no runtime hot-path change expected; confirm neutrality).
- A/B levers: `B3_FOLD_TRIGGER_DISABLE` flips the 2 Float targets; `B3_DISABLE`/`B3_SPAN_DISABLE` flip Bool as on base.

---

## §7 Risks

- **R1 — Symbol-count growth.** Distinguishing fold `lo_pos` adds distinct `(nt,lo,hi)` keys. *Mitigation:* one extra key per fold nesting level (bounded by tokens); measure SPPF node count on the gauntlet + deep tests; the `SPURIOUS_ORPHAN_THRESHOLD=256` and revival budgets bound any revival fallout.
- **R2 — Regressing a previously-collapsing-but-correct case.** Some grammar may *rely* on the fold/operand Symbol collapse. *Mitigation:* the A/B lever + the full op-suite/parity sweep; the change is symmetric across all keyword folds so any breakage surfaces broadly and early.
- **R3 — The forward path still doesn't converge (only the backstop does).** If dedup-distinction alone doesn't make the forward fanout resolve, the parse must rely on revival draining the now-distinct inner body. *Mitigation:* M*.1 explicitly accepts either convergence OR drain; if neither closes it, STOP and reassess (do NOT add weight/threshold).
- **R4 — Welch regression.** Unlikely (arm unreachable by chains) but the trigger-terminal push adds a tiny per-fold SPPF op. *Mitigation:* the N≥51 panel; if non-neutral, scope the `lo_pos` change to multi-arg folds only.
- **R5 — Triple-nested depth.** `test_triple_nested_float` exercises one more nesting level; confirm the dedup-distinction and revival budget scale (they're linear in depth).

---

## §8 Critical sites

- `languages/src/calculator.rs:377/383` (`IntBin`/`FloatBin` 2-param folds), `:230-243` (4 unary casts each), `:100-101` (`ProcInt`/`ProcFloat` projections) — the grammar locus (symmetric int/float).
- `prattail/src/sppf.rs:164-172,283-284` — Symbol-dedup `(nt,lo,hi)` keying and the documented unary-prefix `lo_pos` precedent the fix generalizes.
- `macros/src/gen/runtime/wpda_codegen/binder.rs:1015-1190` (`emit_*` BinderRule entry / fold keyword dispatch) + `prefix.rs:1425-1590` (`emit_unified_arm`) + `prattail/src/wpda_runtime.rs` (`TriggerMode`, `min_terminal_span` doc) — where the trigger-anchored `lo_pos` change lands.
- `prattail/src/wpda_walker.rs:5108-5135` (realize `slack < min_span` filter), `:315` (`min_terminal_span` default 0 / `emit_min_terminal_span_body`), `:9049` (`revive_orphaned_cohort_members_once`), `:10421/10443` + `:4143/4170` (retention/revival sites), `:113` (`b3_span_disabled` lever pattern) — the realize/revival backstop and A/B lever.
- `prattail/src/dispatch_cohort.rs:1058` (`take_span_anchored_outer_cast`), `:443-449/526` (InFlight orphan registration + `register`) — the drain contract the distinct inner body must satisfy.
