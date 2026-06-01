# Plan: Cluster J (display→parse roundtrip) + Slow-Z campaigns — principled fix

**Repo:** `/home/dylon/Workspace/f1r3fly.io/mettail-rust` (PraTTaIL)
**HEAD at planning:** `12234f9` (= `6507b9c` baseline + `380cc94` cast-family/Cluster-B-gate + `12234f9` docs). **Baseline log `/var/tmp/nextest.log` was captured at `6507b9c`** — i.e. BEFORE the Cluster B gate fix and the cast-family work landed. Every J/slow datum below is from that pre-fix log; the residual after the now-landed fixes is UNKNOWN until re-run.
**Mode:** DESIGN ONLY. No build, no cargo, no file writes during planning. The implementer (later, after the cast-family build frees the 32 GB slot) runs serial foreground builds under `systemd-run --user --scope -p MemoryMax=32G` (16G per test, 8G per campaign), one worktree, self-clean.

---

## §0 — Current Cluster J + slow-Z failure set (from logs) + cascade-from-B reasoning

### 0.1 What changed since the baseline log

The baseline `/var/tmp/nextest.log` (113 fails, HEAD `6507b9c`) predates two landed changes:

- **`380cc94`** — Cluster B **kind-validated chain gate** in `prattail/src/wpda_walker.rs:6228-6248`. Confirmed present in HEAD: the blind `remaining_atoms` gate (which "bled across `)`/`(` and across different-precedence operators, spuriously triggering `synth_binary_chain` on grouped/comparison/mixed-precedence expressions, then desyncing the parse") now delegates to `peek_binary_chain(tokens, cursor.pos, 5)`, firing only on a genuine flat `atom (op atom)*` chain over one `(atom_kind, op_kind)` pair. Prior-session task ledger records Cluster B `completed` with exactly this root cause and the note: **"casts `int(int(..))` = 555-fork explosion, NO absorb (separate)"** and **"bare-var p now Ambiguous(Proc,Name) not parse-fail (uncommitted fix completed parse)"**.
- **`380cc94` + `12234f9`** — Sig-B cast-family cohort work (Blockers B1/B2/B3). The B3 baseline (`/var/tmp/suite-green/b3-BASELINE.txt`) shows nested-cast parsing (`int(int(5,32),32)` PASS; `float(float(10,64),64)` / `float(float(float(10,64),64),64)` were B3 targets).

**Consequence:** the J cluster has NOT been re-run since these landed. The entire plan's M*.0 step is to re-run and measure the CURRENT residual before any edit.

### 0.2 The 24 hard parse-failure J cases (signature `arb_X produced unparseable surface term`)

Extracted from `/var/tmp/nextest.log`. Grouped by the **inner** parser error (the real discriminator), with cascade prediction keyed to the landed B gate fix:

**Sub-cluster J-A — grouped / mixed-arith chains (pure binary-op grammars).** Predicted **CASCADE-GREEN from the B gate fix** (these are the exact shapes the prior ledger lists as fixed):
- `gen_basemath_prop num_display_parse_roundtrip` — `…+ (435626938 + 106629652) + …` → `semantic-action elide / arity mismatch at rule (src=0,rule=0)`. BaseMath grammar is only `Add`/`Sub` (`languages/src/composition/base_lang.rs`); input is a legal `+`/`-` chain with a grouped subterm.
- `gen_extmath_prop num_display_parse_roundtrip` — `892679477 + … + (…)` → same elide signature. ExtMath `extends: [BaseMath]`, same grammar.
- `gen_importedmath_prop num_display_parse_roundtrip` — `170657606 + (913311354 + 765960175 + (…))` → `expected ) to close grouping at pos 6, found +`. ImportedMath adds `Div`.
- `gen_mixedmath_prop int_display_parse_roundtrip`, `gen_mixedmath_prop bool_display_parse_roundtrip` — `-((…)-(…))` → `semantic-action elide at rule (src=1,rule=1)` (the `Neg` prefix + grouped chain).
- `gen_ledtest_prop num_display_parse_roundtrip` (`1793342327 == 1341922371` → `WPDS produced no result`), `expr_display_parse_roundtrip`, `pred_display_parse_roundtrip` (`-475086902 != -1476893613 * (…)` → `WPDS produced no result`). Ledtest has `==`/`!=`/`*` + grouping.
- `gen_calculator_prop bigrat_display_parse_roundtrip` (`(error / …) bitand (… / …) + …` → `no accepting branch … found /`), `bigint_display_parse_roundtrip` (`cast_error_uint bitor bigint(a) bitand -error` → `found cast_error_uint` at 1:1), `bool_display_parse_roundtrip`, `int_display_parse_roundtrip`, `uint32_display_parse_roundtrip` (`816675508 <= … bitand (…)` → `premature lex-Fork acceptance, found <=`), `str_display_parse_roundtrip`. These mix grouped chains + the spec-defined error/cast sentinels (`Err . |- "error"`, `CastErrUInt32 . |- "cast_error_uint"`, etc. — all first-class nullary rules at `languages/src/calculator.rs:114-123`, so they ARE legal surface tokens). The B gate fix is the primary suspect; some may have a residual cast-fork component (see J-B).

**Sub-cluster J-B — nested casts (`int(...)`, `float(...)`, `str(...)` wrapping a cast).** Predicted **PARTIALLY cascade-green from the cast-family B1/B2/B3 work; verify residual**:
- `gen_calculator_prop float_display_parse_roundtrip` — `float(str("") , int(str(cast_error_float)))` → `found ( at 1:6`.
- `gen_calculator_prop int_display_parse_roundtrip` — `int(str(1177855666) , (… ? cast_error_int : …) + … ^ error)` → `found ( at 1:4`.
- `gen_calculator_prop proc_display_parse_roundtrip` — `(… - cast_error_fixed) % … bitand cast_error_fixed` → `found ) at 1:33`.
- `gen_calculator_prop str_display_parse_roundtrip` — `str(… > int(a , cast_error_int))` → `found ( at 1:4`.
- These are the "555-fork explosion, NO absorb" class. The B3 baseline confirms multi-level casts (`float(float(float(...)))`) were the explicit B3 target — so whether these are green now depends entirely on how far B3 transitive cross-wrap splicing landed. **Re-run decides.** (Note: some show a SECOND arg, e.g. `int(str(...) , (...))`; the calculator `int(a)` cast is single-arg; a two-arg `int(x, y)` surface suggests these inputs interleave a comparison/`count`-like form; this is exactly where re-run + the per-input trace is needed before any edit.)

**Sub-cluster J-C — rhocalc / binder-heavy Name·Proc cross-cat (NOT chain-absorbable).** Predicted **MAY partially cascade (B completed bare-var Proc/Name parses); likely some residual**:
- `gen_rhocalc_prop int_display_parse_roundtrip` — `count(a!(error) , -a - ().{error})` → `found identifier a at 1:7`.
- `gen_rhocalc_prop name_display_parse_roundtrip` — `@(a!(error))` → `found identifier a at 1:3`.
- `gen_rhocalc_prop proc_display_parse_roundtrip` — `len(a!(error))` → `found identifier a at 1:5`.
- These exercise `POutput (n "!" "(" q ")")`, `NQuote (@ "(" p ")")`, `Len`, `CountBag` (`languages/src/rhocalc.rs:70-84,756,659`) — Name-category dispatch nested in Proc prefix forms. The master plan's Phase 6.3 constraint says binder-heavy non-canonical-chain grammars are NOT rescued by chain absorption; their tractability comes from (1) the B-completion fix, (2) `semantic_hash`/eqrel dedup, (3) input-bounding. So expect a residual here even after B.

**Sub-cluster J-D — class* smoke grammars (`choose`/`chooseMap` prefix, opt/multi).** Predicted **cascade-mixed; some are genuine Display-vs-grammar (see J-E)**:
- `gen_class2hashmapsmoke_prop proc_display_parse_roundtrip` — `chooseMap a(chooseMap 0(…))` → `found chooseMap at 1:13`.
- `gen_class2optsmoke_prop proc_display_parse_roundtrip` — `choose choose 0 with (0) with (choose a with ())` → `premature lex-Fork acceptance, found with at 1:17`.
- `gen_class3multi_prop proc_display_parse_roundtrip`, `gen_class3multi_prop name_display_parse_roundtrip` (`@(().{(a?a0).{a}with [0|a|0]}with [])` → `found ( at 1:3`), `gen_class3opt_prop proc_display_parse_roundtrip`, `gen_class3opt_prop name_display_parse_roundtrip`, `gen_class2smoke_prop proc_display_parse_roundtrip`, `gen_guardedrho_prop name_display_parse_roundtrip` (`@for(a6 <- @Nil where true()){a!(a)}` → `found identifier a6 at 1:6`), `gen_guardedrho_prop proc_display_parse_roundtrip`.
- `gen_class2multi_prop proc_display_parse_roundtrip` (note the 10.4 s runtime — this one is slow even when failing; flag for the slow-Z timeout interaction).

### 0.3 The genuine roundtrip-MISMATCH J cases (parse SUCCEEDS, structure differs)

These use `if let Ok(parsed)` in the template (Tests 5/6) or the idempotence assert in Test 4, so they are **NOT parse failures** — the parse succeeds and the term canonicalizes differently. **These DO NOT cascade from B** (B is about parse completion, not canonicalization). They are a distinct root cause (§1.2):
- `gen_ambient_prop proc_strong_roundtrip_via_display` — `{a | a | a}` → `{a | a}` (HashBag multiset count 3 → 2).
- `gen_rhocalc_prop proc_strong_roundtrip_via_display` — prior-session evidence: `bitnot {}` → `{}` (minimal input `BitNot(PZero)`); also `{a | a | error}` → variant.
- `gen_class2optsmoke_prop proc_strong_roundtrip` — `choose 0` → `0` (the `Choose` injection wrapper is dropped).
- `gen_guardedrho_prop name_strong_roundtrip` — `@a` → `a`; and `proc_display_parse_roundtrip` idempotence `{{a}}` → `{a}` (singleton-PPar flattening).
- `gen_class2smoke_prop proc_display_parse_roundtrip` idempotence — `choose…(a | a | …)` → fewer elements (`choose choose 0()()` collapse).
- `gen_class2optsmoke_unit unit_class2optsmoke_proc_choosemaybe` — a hand-written unit test asserting the same `choose`-wrapper property; will move in lockstep with the `choose` decision.

### 0.4 NOT actually Cluster J (reclassify — do not fix here)
- `gen_class3multi_prop proc_parse_determinism` — panics at `prattail/src/wpda_runtime.rs:2434 drain_collection: LIFO violation (id 1 is not top, len 3)`. **This is Cluster C** (collection-stack LIFO), master-plan Phase 2 — it merely surfaces under a proptest harness. Exclude from J; cross-reference Phase 2. If Phase 2 has already landed, expect this green on re-run.
- `roundtrip_tests idempotent_int_display`, `roundtrip_tests roundtrip_int_parse_display`, calculator `display_roundtrip_bool_xor_lt` / `test_bool_display_roundtrip_deep_lt` / `test_bool_display_roundtrip_nested_lt` — hand-written (non-generated) roundtrip tests. Likely Cluster B/F (comparison/bool chains); re-run will show if cascade-fixed. Track but treat as B/F residual, not J-template.

### 0.5 Slow-Z (2 campaigns)
From `/var/tmp/nextest.log` lines 15332-15434:
- `gen_calculator_prop sim_calculator_proptest_campaign` — **PASSED at 1391.9 s** (known-good; NOT a hang). Within the existing 1800 s ci-override cap.
- `gen_ambient_prop proc_display_parse_roundtrip` — HUNG, last seen `>1980 s`, never completed.
- `gen_rhocalc_prop sim_rhocalc_proptest_campaign` — HUNG, last seen `>1980 s`, never completed.

**Critical correction to the master-plan premise:** `.config/nextest.toml` **already exists** (committed in `380cc94`, dated 2026-05-29) with the bounded profile: `default` 60 s×3 = 180 s; `ci` 120 s×5 = 600 s general, with a `proptest_campaign|display_parse_roundtrip` override at 180 s×10 = **1800 s cap**. So Phase 6.1 (infra) is DONE. The two hangs exceed 1800 s → they now FAIL LOUDLY (terminated) rather than stalling the suite. The slow-Z work is therefore purely **root-cause + input-bounding** so they complete within cap, not infra.

---

## §1 — Root cause per sub-cluster

### 1.1 J parse-failures (J-A/B/C/D) — DOWNSTREAM of Cluster B (+ cast-family), now substantially landed
The `*_display_parse_roundtrip` template (Test 4, `macros/src/gen/test_gen/strategies.rs:1402-1435`) was **deliberately strengthened from silent-skip to hard-panic** on any parse failure ("Any parse failure here is a real regression — the generator emitted something the grammar does not admit"). The generator emits only spec-derived surface forms (`generate_literal_build_code` projects literals onto the grammar's admitted domain — `strategies.rs:485-576` — and `classify_variants` emits `compile_error!` rather than fabricating an unparseable leaf — `strategies.rs:449-458`). The error sentinels (`error`, `cast_error_*`) ARE spec rules. **Therefore every J-A/B/C/D input is, by construction, a legal surface term, and a parse failure is a parser-completion bug — i.e. Cluster B.** The landed kind-validated gate (`wpda_walker.rs:6228`) is the primary fix for J-A; the cast-family B1/B2/B3 work is the fix for J-B; J-C/J-D are the binder-heavy/prefix residual that the B-completion fix partially addresses. **No J-A/B/C/D fix should be designed before re-run** — the principled position is that these are not a separate defect class, they are the same Cluster-B defect observed through the proptest lens, and the only legitimate post-re-run work is (a) confirm green, or (b) for a genuine residual, a targeted parser-completion fix subject to the HARD INVARIANT (restore completion, never narrow the cursor set), or (c) if a specific surface form is genuinely ambiguous, accept the alternative set in the expectation.

### 1.2 J roundtrip-mismatches (§0.3) — genuine grammar canonicalization, NOT a parser defect
The mismatches are all **observational-equivalence collapses that the grammar legitimately performs**:
- **HashBag multiset**: `PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}"` (`rhocalc.rs:72`, `ambient.rs:27`). `HashBag` is a **multiset** (`runtime/src/hashbag.rs`: "tracks the count of each unique element… Equality is based on element counts"). `{a | a | a}` is count{a:3}; if the parser builds count{a:2}, that is a parser bug (a dropped duplicate). BUT if the language INTENDS parallel composition to be set-like at a given nesting, the collapse is correct and the TEST EXPECTATION is wrong. The `{{a}}`→`{a}` case is singleton-PPar flattening (a `PPar` of one element ≡ that element) — a deliberate canonicalization.
- **Injection/prefix wrappers**: `choose 0`→`0`, `@a`→`a`, `bitnot {}`→`{}`. These are AST injection constructors (`Choose`, `NQuote`, `BitNot` on `PZero`) whose Display emits a prefix that the parser canonicalizes away (or whose Display should not have emitted the wrapper for that operand). `BitNot(PZero)` at depth-1 displaying `bitnot {}` but reparsing to `{}` means either Display emits `bitnot` where the grammar can't reattach it to `{}`, or the parser drops it.

**The discriminator (decided per case at implementation M2/M3, NOT now):** for each mismatch, compute `semantic_hash(left)` vs `semantic_hash(right)` (the existing observational-equivalence key, per `f13-stage-2-3-semantic-hash.md`).
- If `semantic_hash` EQUAL → the two displays are observationally equivalent; the grammar's canonicalization is correct; **fix the TEST EXPECTATION** to compare canonical (post-parse) forms, not raw display, for that category (this is the HARD-INVARIANT-sanctioned path: "if the grammar is genuinely ambiguous/canonicalizing, fix the EXPECTATION to accept the alternative set, never weaken the parser").
- If `semantic_hash` DIFFERS (e.g. multiset count genuinely lost) → it is a real parser-construction or Display bug; fix the offending side **without** collapsing distinct alternates (e.g. fix the HashBag `*sep("|")` builder to preserve multiplicity, or fix the prefix Display BP). NEVER "fix" by making the parser drop the wrapper to match.

These mismatches are a **small, bounded set** (~5-7 generated tests + 1 unit test) and are independent of B; they are the genuine residual the master plan's Phase 7.1 option (a)/(b) anticipated.

### 1.3 Slow-Z hangs — binder-heavy proptest blow-up, NOT a B parse cascade
- `gen_rhocalc_prop sim_rhocalc_proptest_campaign` (`macros/src/gen/test_gen/simulation_tests.rs:315-372`, `with_cases(50)`, `arb_proc(3u32)`). The campaign wraps the run in `catch_unwind` and tolerates ALL outcomes except `InvariantViolation` — so it does NOT hang on parse failures (those are caught). The hang is the **rewrite engine / Ascent eqrel-closure** on deep random rhocalc terms (`run_to_normal_form`), and/or the `BoundedSize{max_nodes:10000}`/`BoundedDepth{max_depth:50}` exploration cost across 50 cases. Per Phase 6.3 + the F.13 standing result, rhocalc is non-canonical-chain/binder-heavy, so chain absorption does NOT help; tractability comes from `semantic_hash`/eqrel dedup at the rhocalc boundary and from clamping the input magnitude/depth.
- `gen_ambient_prop proc_display_parse_roundtrip` (`strategies.rs:1402`, `with_cases(100)`, `arb_proc(3)`). This is a roundtrip test, but it HANGS rather than failing — meaning a *specific generated ambient term* drives the PARSER (`Proc::parse`) into a blow-up (cursor/SPPF explosion on a deeply-nested `PPar`/`PAmb`/`PNew` term), OR Display itself is super-linear. The B gate fix may reduce this (fewer spurious cursors); whether it now completes within 1800 s is unknown. The candidate root is parser cursor explosion on nested HashBag-PPar (the `*sep("|")` collection inside `*sep` ambient nesting), which the `hang-dump` feature (`PRATTAIL_HANG_DUMP=1` + `--features hang-dump`, SIGUSR1) is designed to diagnose.

Two orthogonal mitigations, both honoring the invariant (neither drops an alternate):
- **(a) Input-bounding** (`strategies.rs` `arb_*` / tape projection + `with_cases`): clamp generated term depth/magnitude and thread `PROPTEST_CASES` so the campaign's intrinsic cost is bounded. This is a TEST-INPUT change, no product behavior, no Welch.
- **(b) Root-cause dedup**: if the trace shows Ascent eqrel-closure divergence (rhocalc) or cursor explosion (ambient), apply the existing `semantic_hash` + outer-discriminant dedup at the rhocalc normal-form boundary / parser cohort — dedup ONLY observationally-equivalent states (never plain Display-dedup; the `-3!` lesson). This is a runtime-behavioral change → Welch + op-suites + disambiguation gate required.

---

## §2 — The principled fix(es)

**Overarching principle:** the largest part of J is hypothesized already-green (cascade from the landed B gate + cast-family). The plan front-loads measurement so the implementer fixes ONLY the true residual, and every residual fix is forced into one of three invariant-safe shapes: (i) parser-completion restoration (never cursor narrowing), (ii) test-expectation alignment for genuine canonicalization (compare semantic_hash / canonical form), or (iii) test-input bounding for slow campaigns. The forbidden shape — making the parser/eval drop an alternate to force a match — is explicitly excluded.

### Fix 1 — J parse-failures: re-run, confirm cascade, fix only residual (§1.1)
- **M1.0 establishes the residual.** For any case still failing:
  - **J-A residual** (grouped/mixed arith still failing): trace with `--features mettail-prattail/walker-stats --no-capture` on the minimal input; inspect `chain_earley_trigger_count` / `chain_earley_returned_none_count`. If the gate now correctly does NOT trigger but completion still fails, the residual is the chart-completion gap the master plan's Phase 3 reserved (`complete_to_fixpoint` retired to dead_code) — revive equivalent inline completion for the sub-4-atom/non-chain case. **Restore completion; do not narrow the cursor/alternative set.**
  - **J-B residual** (nested casts): this is the cast-family B3 transitive cross-wrap frontier (see the `prattail/docs/design/plans/sigb-blocker3-*.md` design docs). If B3 transitive splicing has not fully landed, J-B residual is expected and is OUT OF SCOPE for this plan — record it as blocked-on-B3, do not attempt a J-local hack.
  - **J-C/J-D residual** (binder-heavy / prefix): targeted parser-completion for the specific Name·Proc cross-cat / prefix nesting, same invariant. If a specific surface form is genuinely ambiguous (two valid parses), change the template's Test 4 to accept the `Ambiguous` alternative set rather than forcing one.
- No product change is made speculatively; if re-run is fully green, Fix 1 is a no-op (record the cascade).

### Fix 2 — J roundtrip-mismatches: semantic_hash triage → expectation OR construction fix (§1.2)
- For each of the ~5-7 mismatch cases, the implementer computes `semantic_hash(displayed)` vs `semantic_hash(canonical)`:
  - **Equal** → fix the **generated test template** so the strong/idempotence comparison is on the canonicalized form, not raw display, for canonicalizing categories. The single source of truth is `macros/src/gen/test_gen/strategies.rs`: Test 5 binder branch at `:1474-1494` (`strong_roundtrip_via_display`, asserts `displayed == re_displayed` at `:1488`), Test 5 non-binder at `:1445-1471`, and Test 4 idempotence at `:1429-1431`. The fix is to assert observational equivalence (parse→display→parse stability, which the template ALREADY computes as `canonical`/`recanonical`) rather than raw-display identity for multiset/injection categories — i.e. drop the `displayed == re_displayed` raw-equality leg where the category is canonicalizing, keeping the `canonical == recanonical` idempotence leg (which is the correct contract). This is a TEST-EXPECTATION fix, no product change, no Welch. It regenerates all `gen_*_prop.rs` (every language), so the op-suite regression gate is mandatory.
  - **Differs** (genuine loss, e.g. multiset count) → fix the offending **product** side: either the HashBag `*sep("|")` parse-construction (preserve multiplicity) or the prefix-operator Display BP in `macros/src/gen/syntax/display.rs` (emit/withhold the wrapper consistently with the grammar). This is a product change → gauntlet + op-suites + Welch (if a parse/Display hot path) + disambiguation gate. NEVER collapse a distinct alternate to match.
- Keep the hand-written `unit_class2optsmoke_proc_choosemaybe` in lockstep with the `choose` decision.

### Fix 3 — Slow-Z: bound inputs, then root-cause if still over cap (§1.3)
- **3a (infra, already partly done):** `.config/nextest.toml` exists with the 1800 s cap. Thread `PROPTEST_CASES` into the generated `with_cases(N)` so triage can run reduced (e.g. `PROPTEST_CASES=8`) while CI keeps full coverage. Sites: `macros/src/gen/test_gen/strategies.rs:1366` (`with_cases(100)` for the roundtrip block) and `macros/src/gen/test_gen/simulation_tests.rs:317` (`with_cases(50)` for the campaign). Implement as `ProptestConfig::with_cases(std::env::var("PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(100))` (resp. 50). Test-codegen only, no product behavior, no Welch. Regenerates all `gen_*` files → op-suite gate.
- **3b (input magnitude/depth clamp):** in `strategies.rs` `arb_*` (the tape size at `:1350`, `max_tape = (10*(max_depth+1)).max(20)`) and the literal projection (`generate_literal_build_code`, `:485-576`), clamp generated bignum magnitude/exponent and term depth so the rewrite engine's intermediates stay bounded. Test-input fix, no Welch.
- **3c (root-cause, only if still over cap after 3a/3b):** run the offending campaign under reduced `PROPTEST_CASES` with `walker-stats` (ambient parser path) or rhocalc eval instrumentation; for a hang, `PRATTAIL_HANG_DUMP=1 --features hang-dump` then SIGUSR1 (never SIGUSR1 without the feature). If ambient shows parser cursor explosion → the residual is a B-completion / cohort-dedup issue: apply `semantic_hash` + outer-discriminant dedup at the cohort boundary (dedup only observationally-equal cursors). If rhocalc shows Ascent eqrel-closure divergence → apply `semantic_hash` dedup at the `normal_forms()` boundary (`runtime/src/language.rs:402`). Both are runtime-behavioral → Welch + op-suites + disambiguation gate. Per Phase 6.3, do NOT expect chain absorption to help these; closing the general WPDS exponent is explicitly OUT OF SCOPE.

---

## §3 — Milestone breakdown (M*.0 = measure-first; gauntlet + op-suite gate after EVERY change)

**Universal per-change gate (run after each milestone that changes any file):**
1. Gauntlet: `cargo test --release -p mettail-prattail --lib` → expect 4220/0 (HEAD baseline per b3 logs; the master plan's "4206" predates cast-family).
2. Op-suites: `cargo nextest run -p mettail-languages --test gen_calculator_op --test gen_rhocalc_op --test gen_calculator_unit --test gen_rhocalc_unit` → no NEW fails (gen_rhocalc_op 532/0; gen_calculator_op ≥1331 per b2 final).
3. Disambiguation-preservation: `-3!` ambiguity-ladder (`edge_case_tests` + `probe_neg_zero` 23/0) + `wpda_parity_calculator` / `wpda_parity_calculator_cross_cat` / `wpda_parity_lambda` stay green.
4. Welch (p<0.05, QUIET, N≥15, release) ONLY for runtime-behavioral changes (Fix 2-differs, Fix 3c). Not for test-template/test-input/test-expectation changes.

All builds: serial foreground, `systemd-run --user --scope -p MemoryMax=32G` (16G per individual test, 8G per campaign), one worktree, self-clean. Tee every expensive run to `/var/tmp/suite-green/cjz-<milestone>-*.log`.

### M0 — Re-run to establish CURRENT residual (NO code changes) — load-bearing
- **M0.0** Build the `mettail-languages` test artifacts once (foreground, capped). Then run the full J suite targeting only the J binaries:
  `cargo nextest run -p mettail-languages -E 'test(/_display_parse_roundtrip/) | test(/_strong_roundtrip/) | test(/_parse_determinism/)' --profile ci 2>&1 | tee /var/tmp/suite-green/cjz-m0-jsuite.log`.
- **M0.1** Classify the residual against §0.2/§0.3: mark each of the 24 parse-failures + 5-7 mismatches as {cascade-green / residual-parse / residual-mismatch / reclassified-C-or-B-or-F}. Confirm `gen_class3multi_prop proc_parse_determinism` is Cluster C (or green if Phase 2 landed).
- **M0.2** Slow-Z probe (bounded): run the 2 hangs ALONE under the ci profile with the 1800 s cap, capped at 8 G:
  `cargo nextest run -p mettail-languages -E 'test(gen_ambient_prop::proc_display_parse_roundtrip) | test(gen_rhocalc_prop::sim_rhocalc_proptest_campaign)' --profile ci 2>&1 | tee /var/tmp/suite-green/cjz-m0-slowz.log`. Record: complete-within-cap vs terminated; capture timing.
- **Gate:** record the residual table in the ledger. **No fix milestone (M1-M3) starts for a sub-cluster until M0.1 confirms it has a residual.** If M0 is fully green for a sub-cluster, that sub-cluster's milestone is a documented no-op (cascade win).

### M1 — J parse-failure residual (only if M0.1 shows residual) — Fix 1
- **M1.0** Re-confirm the specific residual set from M0.1 (no change yet).
- **M1.1** Per residual family, trace (`walker-stats` / minimal input) to localize: chart-completion gap (J-A) vs B3-transitive (J-B, likely OUT OF SCOPE → record blocked) vs Name·Proc completion (J-C/D).
- **M1.2** Apply the minimal parser-completion fix in `prattail/src/wpda_walker.rs` (revive equivalent completion for the residual case) — **restore completion, never narrow cursors**. If a form is genuinely ambiguous, instead change Test 4 in `strategies.rs` to accept the `Ambiguous` set.
- **Gate:** universal gate (1-3) + re-Welch the chain panel (chain_50/100/200 LEFT+RIGHT, release) — the landed WALK-S0..S3 wins must not regress (R2). Re-run the J suite + the H/recovery + slow-Z probes (siblings of B).

### M2 — J roundtrip-mismatch residual — Fix 2
- **M2.0** Re-confirm the mismatch set from M0.1; for each, compute `semantic_hash(displayed)` vs `semantic_hash(canonical)` (a tiny throwaway harness inside the existing test binary, or read the minimal-failing-input AST already printed in the log).
- **M2.1 (equal → expectation fix):** edit the generated test template in `macros/src/gen/test_gen/strategies.rs` (Test 4 idempotence `:1429`, Test 5 binder `:1488`, Test 5 non-binder `:1458-1465`) to assert canonical-form idempotence (the already-computed `canonical == recanonical` leg) for canonicalizing categories, dropping the raw-display-identity leg where it conflicts with legitimate canonicalization. Update `unit_class2optsmoke_proc_choosemaybe` in lockstep.
- **M2.2 (differs → construction fix):** fix the HashBag `*sep` parse-construction or the prefix Display BP in `macros/src/gen/syntax/display.rs` to preserve the distinct value — never collapse alternates.
- **Gate:** universal gate (1-3). M2.1 is test-only (no Welch). M2.2 is a product change → add Welch (parse/Display hot path) + disambiguation gate. Regenerate-all → full op-suite gate is mandatory (template change touches every `gen_*_prop.rs`).

### M3 — Slow-Z bounding + (conditional) root-cause — Fix 3
- **M3.0** From M0.2: if both campaigns already complete within the 1800 s cap, M3 reduces to wiring `PROPTEST_CASES` (defense-in-depth) only.
- **M3.1 (infra):** thread `PROPTEST_CASES` into `with_cases` at `strategies.rs:1366` and `simulation_tests.rs:317`. Regenerate-all → op-suite gate. No Welch.
- **M3.2 (input clamp):** clamp bignum magnitude/exponent + term depth in `strategies.rs` `arb_*`/`generate_literal_build_code`/tape sizing (`:1350`, `:485-576`). Re-run the 2 campaigns under the cap. No Welch (test-input).
- **M3.3 (conditional root-cause):** ONLY if still over cap after M3.1/M3.2. Trace with `walker-stats` (ambient) / hang-dump and apply `semantic_hash` + outer-discriminant dedup at the cohort boundary (ambient parser) or `normal_forms()` boundary (rhocalc, `runtime/src/language.rs:402`) — observational equivalence only.
- **Gate:** M3.1/M3.2 test-only. M3.3 runtime-behavioral → Welch + op-suites + disambiguation gate.

### M4 — Consolidate + full-suite confirmation
- **M4.0** Re-run the full J suite + slow-Z under the ci profile; confirm 0 J fails and both campaigns within cap.
- **M4.1** Run the universal gate once more; update `memory/2026-05-29-drive-suite-green-ledger.md` (one row per sub-cluster: J-A/B/C/D/mismatch/slow-Z with bucket cascade-from-B / genuine-residual, fix-commit, verify-cmd, gauntlet, op-suites, Welch-id). Finalize the pgmcp experiment for this workstream.

---

## §4 — Invariants (carry through every milestone)

1. **WPDA end-to-end disambiguation is sacrosanct.** No parser-completion fix may narrow the cursor/alternative set to force acceptance — it must RESTORE completion and let EOI/semantic-guard evidence prune (the WALK/Tomita/GSS rationale). Applies to all of M1.
2. **Dedup ⇒ observational equivalence only.** Any dedup (M2.2-differs, M3.3) uses `semantic_hash` + outer-discriminant tagging (`f13-stage-2-3-semantic-hash.md`), NEVER plain Display-dedup. The `-3!` lesson: `Int::Fact(NumLit(-3))` ("error") vs `Int::Neg(Fact(3))` ("-6") both Display `-3!` and must stay distinct.
3. **`Ambiguous` is first-class.** If a residual J input is genuinely ambiguous, the fix is to accept the alternative set in the test expectation, never to collapse to one parse.
4. **Test-expectation changes are the sanctioned path for genuine grammar canonicalization** (M2.1) — compare `semantic_hash`/canonical-idempotence, not raw display. This is NOT weakening the parser; the parser already produces the correct canonical term.
5. **Disambiguation-preservation gate** (`-3!` ladder + `wpda_parity_*`) green after every milestone.
6. **No silent skips / no delete-to-disable.** A terminated slow test FAILS loudly (the existing nextest.toml comment makes this explicit). Comment-out only with rationale.
7. **Welch (p<0.05, QUIET, N≥15, release)** for every runtime-behavioral change (M1 chain panel, M2.2, M3.3); NOT for test-template/test-input/test-expectation changes.
8. **Measure before edit:** every M*.0 re-runs to establish the current residual before any change in that milestone.

---

## §5 — Risks

| # | Risk | Mitigation |
|---|------|-----------|
| R1 | Baseline log predates B + cast-family → §0 counts are stale | M0 re-run is mandatory and gates all fix milestones; fix ONLY measured residual |
| R2 | M1 parser-completion fix regresses the landed WALK-S0..S3 chain wins | Re-Welch the full chain panel (left/right 50/100/200) after M1; REJECT → revert |
| R3 | Tempting to "fix" a J parse-failure or mismatch by collapsing an alternate | HARD INVARIANT §4.1/§4.2 + disambiguation gate after every milestone |
| R4 | J-B nested-cast residual is the unlanded B3 transitive cross-wrap frontier | Record J-B residual as blocked-on-B3 (see `sigb-blocker3-*.md`); do NOT attempt a J-local hack |
| R5 | Template change (M2.1, M3.1) regenerates ALL `gen_*` files → wide blast radius | Full op-suite gate mandatory after any `strategies.rs`/`simulation_tests.rs` template edit |
| R6 | `gen_class3multi_prop proc_parse_determinism` mis-scoped as J | Reclassified to Cluster C (§0.4); verify against Phase 2 status, do not fix in J |
| R7 | Slow-Z hangs persist after input-bounding (true algorithmic blow-up) | M3.3 trace (walker-stats/hang-dump) → semantic_hash dedup at cohort/NF boundary; per Phase 6.3 do NOT expect chain absorption to rescue binder-heavy grammars; general exponent OUT OF SCOPE |
| R8 | Noisy machine (concurrent cast-family build) → false Welch REJECT | No Welch until the 32 GB build slot is free and the machine is QUIET; σ/μ tell; re-bench |
| R9 | The `mismatch` set is larger than estimated once re-run | M0.1 enumerates the true set before M2; M2 scales to whatever M0 shows |
| R10 | `.config/nextest.toml` cap (1800 s) kills the good 1391 s calc campaign | Already tuned (comment in file); calc campaign passed at 1391 s < 1800 s; do not lower below ~1500 s |
| R11 | HashBag multiset "fix" could silently turn parallel-composition into a set | M2.2 semantic_hash discriminator decides expectation-vs-construction; preserve multiplicity, never set-collapse |

---

## §6 — Critical sites

**Test-generation (the J template + slow-Z campaign + input strategies):**
- `macros/src/gen/test_gen/strategies.rs` — Test 4 roundtrip (`:1402-1435`, hard-panic at `:1419-1422`), Test 5 strong-roundtrip (`:1445-1494`, raw-display assert at `:1458`/`:1488`), Test 6 determinism (`:1500-1529`); `with_cases(100)` (`:1366`); `arb_*` tape sizing (`:1348-1360`); literal projection `generate_literal_build_code` (`:485-576`); leaf classification + `compile_error!` guard (`:432-460`).
- `macros/src/gen/test_gen/simulation_tests.rs` — campaign generator + `with_cases(50)` (`:315-372`, esp. `:317`); `catch_unwind`/tolerate-all (`:356-371`).

**Parser (J parse-failure residual = Cluster B locus):**
- `prattail/src/wpda_walker.rs` — landed kind-validated chain gate (`:6228-6248`, `peek_binary_chain`); `resolve_at_end_of_input` reject sites (`:4272` premature-lex-Fork, `:4324` no-accepting-branch); semantic-action elide emission (`:12002-12008`); retired `complete_to_fixpoint`/`earley_outboard_chain` dead_code (revival candidate for J-A residual).

**Display + grammar (J mismatch + slow-Z ambient):**
- `macros/src/gen/syntax/display.rs` — trampolined Display + prefix/infix BP (`DisplayBpInfo`/`DisplayPrefixBpInfo` `:36-173`); prefix-operator parenthesization (mismatch root for `bitnot`/`@`/`choose`).
- `languages/src/rhocalc.rs` (`PPar` HashBag `:72`, `POutput`/`NQuote`/`PDrop`/`Len`/`CountBag` `:70-84,756,659`, `BitNot` `:221`), `languages/src/ambient.rs` (`PPar` HashBag `:27`), `languages/src/calculator.rs` (error/cast sentinels `:114-123`, casts `:230-245`) — the grammars whose canonicalization (multiset, singleton-flatten, injection) defines the correct M2 expectation.
- `runtime/src/hashbag.rs` — multiset semantics (count-based equality); the authority for the `{a|a|a}` vs `{a|a}` decision.

**Infra + dedup:**
- `.config/nextest.toml` — ALREADY EXISTS (1800 s campaign cap); slow-Z infra is done.
- `runtime/src/language.rs:402` — `normal_forms()` boundary (rhocalc M3.3 semantic_hash dedup site); `Ambiguous` union (`:36-103`).
