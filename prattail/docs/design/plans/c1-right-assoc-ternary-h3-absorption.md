# PraTTaIL C1-R + C1-M (REVISED): generalize H3 chain absorption to right-associative binary (`^`) and mixfix ternary (`? :`) via canonical-op eligibility + a pre-fork right-recursive trigger + direct SPPF synthesis

Branch `feature/wfst-architecture`, base tip `a23ef69` (WALK-S1.5 diagnosis committed). pgmcp experiment #8 / hypothesis #8 is the decision record (`primary_metric = ternary_chain_10000_peak_rss_mb`, Welch-t, tail=less, alpha=0.05, min effect cohens_d=0.5). Ledger: `prattail/docs/design/plans/chain-10000-experiments-ledger.md`.

This plan was produced by a Plan agent (2026-05-28) AFTER the WALK-S1.5 diagnosis. It supersedes the prior direct-synthesis-only sketch. That sketch's substrate findings (F1–F10) and synthesis designs are verified-correct and **reused verbatim** where cited. What it MISSED — and what this revision adds — are the two empirically-confirmed mechanisms D1 (cross-category fanout) and D2 (right-recursion never triggers absorption). Those are the spine of this revision.

## 0. Verified findings that drive the design (re-confirmed in-tree at tip `a23ef69`)

**V1 — Per-cursor, per-category dispatch (the D1 mechanism).** The InfixLoop dispatch (`engine_impl.rs:1008-1183`) computes `state_cat_src_idx` from `frontier_top.symbol.category_src_idx` and builds `__cands` from THAT category's `infix_bp_<cat>`/`postfix_bp_<cat>`/`mixfix_bp_<cat>` tables only. `__cands.len() > 1` is multi-TIER ambiguity within one category, NOT multi-category. Cross-category ambiguity is realized as SEPARATE cohort cursors, one per numeric category, each running its own InfixLoop, reconciled at EOI by lex-min over `(primary, src_idx, rule_idx)` + `merge_equivalent_cursors`. A bare integer `1`/`2` is polymorphic (`TokenKind::Integer`): `home_polymorphic_token_arm` (`prefix.rs:41-90`) seeds BOTH an Int cursor and a BigInt cursor. H3 absorption mutates ONE cursor (`cursor.pos=chain_end`+Unwinding, `wpda_walker.rs:5584-5607`), bypassing the per-step Tomita merge. If >1 numeric category is iter-eligible for the same terminal, multiple cursors each jump independently → "no accepting branch reached end of input". AddInt-only is safe because exactly ONE category absorbs; the BigInt cursor stays on the normal walker and is lex-dominated/merged at EOI.

**V2 — Category source-index order + the lex-min winner (CORRECTED 2026-05-29).** `category_src_idx` is assigned by FIRST-RULE-LHS-APPEARANCE in `terms {}` (`collect_category_names_with_literals`), NOT by `types {}` order. The ground truth (generated `WPDA_CATEGORIES`) is: Proc=0, **BigRat=1, Int=2, UInt32=3**, Fixed=4, Float=5, BigInt=6, Bool=7, Str=8, List=9, Bag=10, Map=11 — BigRat=1 because `Err . |- "error" : BigRat` is the first numeric-result rule. So "lowest `category_src_idx`" is WRONG: for `+` it selects AddBigRat (BigRat=1), excluding AddInt (Int=2) — the WALK-S0 bug. The walker's actual lex-min winner is **Int**, because a literal-home prefix arm has tier 0.0 (`lex_w(0.0,…)`) while a cross-cat projection has tier ≥ 0.025; among the integer-home categories {Int=2, UInt32=3, BigInt=6} (all emit the bare-`TokenKind::Integer` home arm) Int has the lowest src_idx, and BigRat reaches a bare integer only via a cross-cat projection (worse tier). The canonical rule therefore needs a PRIMARY key — `value_home_rank` (0 if the category is integer-home, else 1) — BEFORE src_idx. See §2.

**V3 — Operator multiplicity (`calculator.rs`).** `+`: AddInt(Int=1), AddUInt32(2), AddBigInt(3), AddBigRat(4), AddFixed(5), AddFloat(6), AddStr(8) → canonical **AddInt**. `^`: PowInt(Int=1, `step right`), PowFloat(Float=6, `step right`) → canonical **PowInt** (bare `2` doesn't match Float). `?`/`:`: **Tern(Int=1) only** → trivially canonical.

**V4 — Right-assoc binary recurses, never re-iterates (the D2 mechanism).** `analyze_binding_powers` (`binding_power.rs:443`) assigns right-assoc `(prec+1, prec)` → `left_bp > right_bp`. The singleton emits `IterativeChainAbsorb{new_state=InfixChainIterative{rhs_bp}}` (`engine_impl.rs:1151`); the `InfixChainIterative` arm does `Advance(PrefixDispatch{cur_bp: rhs_bp})` (`engine_impl.rs:1232`) — dispatches the RHS sub-parse and never returns to a singleton on the same op-kind for a right-assoc chain. The singleton fires AT MOST once per chain; the walker peek-loop never gets a second iteration. The walker H3 trigger is reachable only through the singleton, so it is equally unreachable for `^`. **A new trigger that fires at the FIRST `^` dispatch, before recursion, is required.**

**V5 — Mixfix associativity is hardcoded `Left`.** `classify_mixfix`/`classify_postfix_mixfix` (`infix.rs:282/271`) set `associativity: Left` unconditionally; `step right` on `Tern` does NOT propagate to `associativity()` for mixfix. Ternary right-recursion is STRUCTURAL: detect via `right_recursive_tail()` (last `MixfixPart.operand_category == result_category` AND `category == result_category`), NOT bp.

**V6 — Ternary `mixfix_parts` shape.** `Tern . c "?" t ":" e`: `mixfix_parts.len()==2`: part[0]={operand `t`, preceding=[], following=[":"]}, part[1]={operand `e`, preceding=[], following=[]}. `c` is the LHS (already-parsed prefix), NOT in `mixfix_parts`. Three operands at synth: `c` (LHS), `t` (part[0]), `e` (part[1]).

**V7 — The chart-based emit is latently wrong (prior F7).** `earley_outboard_chain` maps chain_step/chain_base/atom all to bare `outer_rule_idx` (not `(cat<<16)|rule`, not NumLit for atoms) + includes the op as a Terminal (3 children vs arity-2). Masked for AddInt by parse-only gate + `+` associativity. Replace with direct synthesis.

**V8 — Eval gate idiom (for G4).** `let parsed = lang.parse_term(input).expect(...); let results = lang.run_ascent(parsed.as_ref()).expect(...); let nfs: Vec<String> = results.normal_forms().iter().map(|nf| nf.display.clone()).collect(); assert!(nfs.iter().any(|d| d == EXPECTED));`. Trampoline chain tests use `Int::parse_structured` (parse-only); G4 adds `CalculatorLanguage`+`parse_term`+`run_ascent` value asserts.

## 1. Approach (direct synthesis, no Earley chart)

Recognition by the existing forward peek-loop (`wpda_walker.rs:11730-11757`, O(N), zero-alloc); SPPF by direct synthesis (`synth_atom_symbol`+`synth_binary_chain`+`synth_ternary_chain`). The `earley.rs` chart module is RETAINED (additive, 17 tests); `earley_outboard_chain`+walker `complete_to_fixpoint` become `#[allow(dead_code)]`. ADDED over the prior synthesis design: (1) canonical-op-per-terminal eligibility (D1); (2) a pre-fork right-recursive absorption trigger at the InfixLoop binary AND mixfix tiers (D2); (3) `IterAbsorbSpec` carries canonical/assoc/mixfix metadata + atom literal rule.

## 2. D1 fix — canonical-op-per-terminal eligibility

**Selection rule (CORRECTED 2026-05-29).** Canonical = the iter-eligible operator minimizing `(value_home_rank, category_src_idx, label)`, smallest-first, among all iter-eligible operators sharing the same `terminal`:
1. `value_home_rank(cat)` = 0 if `cat` parses this terminal's operand token via a tier-0.0 polymorphic literal home prefix arm (today: `NativeType::is_integer()` categories, incl. `CanonicalBigInt`), else 1. Mirrors `LexicographicWeight`'s primary key (tier 0.0 home vs ≥0.025 cross-cat).
2. `category_src_idx` — the lex-min tiebreak among equal-rank cursors.
3. `label` — deterministic total order (cannot tie across distinct categories sharing a terminal).

Yields **Int** for `+`,`^`,`?` (Int is integer-home rank 0, lowest src among {Int=2, UInt32=3, BigInt=6}; BigRat=1 is rank 1 → loses despite lower src). Implemented as `BindingPowerTable::is_canonical_iter_op(op, cat_src_idx, value_home_rank)` (binding_power.rs); `value_home_rank` supplied by codegen from `language.types` native kinds (infix.rs `cat_is_value_home`). Pinned by 3 unit tests.

**Soundness (D1).** With canonical eligibility, for any chain over terminal `t`, exactly one cursor (canonical category `c*` = the lex-min winner) absorbs; every other category cursor stays on the normal Tomita-GLR/cohort walker and converges/merges at EOI as in the AddInt-only pilot. `c*` is lex-min-selected at EOI because the `(value_home_rank, src_idx)` keys are precisely the lead components of the walker's `lex_cmp` for the cursors that can parse `t`'s operand. So the accepting parse is the canonical-category parse, identical (modulo absorption) to the pre-broadening parse. □

**Where computed:** `is_canonical_iter_op(op, cat_src_idx)` on `BindingPowerTable` (cross-category terminal scan), called in `emit_iter_eligible_fn` (`infix.rs:475`) as a NEW filter layered atop the existing within-category I1 check (`infix.rs:495`, kept). Thread `categories: &[String]` to resolve name→src_idx.

**Broaden `is_iterative_candidate`** (`binding_power.rs:164`, drop `label=="AddInt"`): admit binary `!is_mixfix && left_bp != right_bp` OR mixfix-ternary-shaped (`is_mixfix && mixfix_parts.len()==2 && all preceding empty && last following empty && inner following==1 && right_recursive_tail()`). `right_recursive_tail()`: `category==result_category && last part operand_category==result_category`.

## 3. D2 fix — pre-fork right-recursive absorption trigger

Interception at the InfixLoop dispatch BEFORE the singleton-vs-fork branch (`engine_impl.rs:~1119`), for binary right-assoc `^` (infix tier) and ternary `?` (mixfix tier).

**Decision: suppress-the-fork-entirely** for the canonical right-recursive op when a deterministic chain is detected by forward peek. Justification: the peek proves the region is a deterministic single-op-kind / single-ternary-shape run; a fork at the chain head spawns cursors that either can't complete the chain (no such op in other cats → die) or redundantly re-walk the interior (already suppressed by `pos_in_absorbed_chain_interval`). Suppressing → ONE accepting cursor (cleanest convergence, lowest memory). Gated on the runtime peek succeeding (>=4 atoms / >=2 levels); on peek-failure, fall through to the existing `match __cands.len()` unchanged (non-chain + short-chain workloads bit-identical). Falsifier: if suppression drops a genuine alternative, G2/G4 catch → fall back to canonical-absorbs-while-others-normal (don't clear `__cands`).

LEFT-assoc binary (AddInt) continues through the EXISTING singleton fast-path (genuinely iterates, ships 112 MB) — NOT routed through the new pre-fork trigger (minimal blast radius).

**Trigger codegen** (after `__cands` built, before `match __cands.len()`): consult `iter_eligible_<cat>(lead_rs, lead_ri) -> Option<IterAbsorbSpec>` for the leading candidate; if `Some(spec)` and (`spec.assoc_right || spec.is_mixfix`), run the forward peek (`peek_binary_chain` / `peek_ternary_chain`); on success `return WpdaStepAction::IterativeChainAbsorb { symbol: lead.symbol, weight: lead.weight, new_state: Unwinding, spec }` (fork suppressed). `_pos` is ON the operator/trigger; LHS head atom already parsed (on `cursor.sppf_stack_id`).

**Peeks** (free fns in `wpda_walker.rs`): `peek_binary_chain(tokens, op_pos, min_atoms)` (hoist existing op-kind peek; head atom at op_pos-1); `peek_ternary_chain(tokens, trigger_pos, trigger_tag, sep_tag, min_levels)` (pattern `[?, atom, :, atom]*` then final `e`; tags via `token_kind_to_tag`). Both O(N), zero-alloc.

**`iter_eligible_<cat>` widened** to `Option<IterAbsorbSpec>` (`emit_iter_eligible_fn` + `emit_iter_eligible_dispatch`). `IterAbsorbSpec` (in `binding_power.rs`, `#[derive(Clone,Copy,Debug)]`): `left_bp, right_bp, assoc_right (left_bp>right_bp), is_mixfix, op_cat_src_idx, op_rule_idx, atom_cat_src_idx, atom_lit_rule_idx (per_cat[atom_cat][0]=NumLit), trigger_tag, sep_tag`. `WpdaStepAction::IterativeChainAbsorb` gains `spec: IterAbsorbSpec` (+ `mem_attr` arm).

## 4. SPPF synthesis (verified intern API)

`intern_terminal(kind, PosOrSynth::Real(pos), text, false)`; `intern_symbol(nt_tag, lo, hi)`; `intern_packing((cat<<16)|rule, children, weight)`; `link_packing_to_symbol`. `realize_packing_call` filters TriggerTerminal children only; arity = non-trigger children.

**`synth_atom_symbol(pos, atom_cat, atom_lit_rule)`**: intern_terminal → intern_packing(`(atom_cat<<16)|atom_lit_rule`, [term], one) → intern_symbol(atom_cat, pos, pos+1) → link → return sym. Idempotent (dedup). Realizes to `Int::NumLit(v)`.

**`synth_binary_chain(head_pos, tokens, spec)`**: recover atom positions `a[0..m]` + `chain_end` by peek; `R=(op_cat<<16)|op_rule`, `w=lex_w(BP_TIER_INFIX, op_cat, op_rule)`. Right-nested (`assoc_right`): `acc=synth_atom(a[m-1])`; for `i in (0..=m-2).rev()`: `pack=intern_packing(R,[synth_atom(a[i]), acc], w); sym=intern_symbol(op_cat, a[i], acc_hi); acc=sym`. Left-nested (`!assoc_right`, AddInt): `acc=synth_atom(a[0])`; for `i in 1..m`: `pack=intern_packing(R,[acc, synth_atom(a[i])], w); sym=intern_symbol(op_cat, a[0], a[i]+1); acc=sym`. Returns `(root, w^(m-1), chain_end)`.

**`synth_ternary_chain(head_pos, tokens, spec)`**: walk per level `c_i,t_i` + final `e_final`; `levels=k>=2`; `T=(op_cat<<16)|op_rule`, `w=lex_w(BP_TIER_MIXFIX, ...)`. `acc=synth_atom(e_final)`; for `i in (0..=k-1).rev()`: `pack=intern_packing(T,[synth_atom(c_i), synth_atom(t_i), acc], w); sym=intern_symbol(op_cat, c_i, acc_hi); acc=sym`. 3 operands only (no `?`/`:` children). Returns `(root, w^k, chain_end)`. Realizes `Tern(c0,t0,Tern(...,e_final))`.

**Weight contract** (VERIFIED `earley_outboard_chain` tail): `accumulated=iter_weight^steps`; each step packing carries iter_weight; atoms `W::one_ref()`. Arm multiplies cursor weight by accumulated.

**Walker arm rewrite** (`wpda_walker.rs:5415`): compute `head_pos` (left-assoc singleton: lo-pos of top SPPF Symbol on `cursor.sppf_stack_id`; pre-fork `^`/`?`: `cursor.pos-1`). Dispatch `spec.is_mixfix → synth_ternary_chain` else `synth_binary_chain`. On `Some((root, acc_w, chain_end))`: pop the head-atom Symbol (`pop_one`), push root, `cursor.pos=chain_end` (+ self.pos if deterministic), `multiply_cursor_weight(acc_w)`, record `chain_absorbed_intervals[(op_cat,op_rule)]`, set Unwinding, resolution check. On `None`: legacy fallback (kept). Remove the `earley_outboard_chain` call (→ dead code).

## 5. Substages — hypothesis → changes → gates → falsifier

**Global gate set G (EVERY substage; ALL pass or `git revert`; MUST include the chain tests in `languages/tests/trampoline_tests.rs`):**
- **G1**: `cargo test --release -p mettail-prattail --lib` = 4217/0.
- **G2 (EVAL)**: all 8 `gen_*_op` suites zero failures.
- **G3 (RSS)**: newest `trampoline_tests-*`, `taskset -c 2 RUST_MIN_STACK=2000000000 /usr/bin/time -v`. left_10000 <= 112 MB (no-regression); right_10000 + ternary_10000 is_ok + < 500 MB (target ~160/~280).
- **G4 (EVAL values, NEW)**: trampoline `#[test]`s via `CalculatorLanguage::parse_term`+`run_ascent`+`normal_forms` (V8): `^` `2^2^3`==256 (NOT 64), `3^2^1^1`==9, `2^1^1^1^2`==4; ternary `0?1:0?1:0?1:0?1:0`==0, `1?7:0?9:3`==7, `0?7:1?9:3`==9; AddInt `1+1+1+1+1+1+1+1`==8; non-triggering oracle `2^3`==8, `1?7:3`==7, `1+1`==2.
- **G5 (Welch)**: LEFT+RIGHT assoc chain_50/100/200, N>=15 quiet runs, Welch p<0.05 vs parent `a23ef69`; no significant slowdown. Samples → pgmcp.
- **Clean-build discipline**: re-confirm on `cargo clean` of macros+prattail+languages on ANY surprising result.

**S0 — `IterAbsorbSpec` + canonical scan + broadened eligibility (scaffolding, NO behavior change).** Hypothesis: introducing the POD + canonical filter + broadened gate + widened `iter_eligible` return, while the singleton still routes ONLY AddInt through the existing chart path and the pre-fork trigger is not yet wired, is behavior-preserving. Changes: binding_power (IterAbsorbSpec, right_recursive_tail, is_canonical_iter_op, broaden is_iterative_candidate), infix.rs (emit_iter_eligible_fn → Option<IterAbsorbSpec> + canonical filter + thread categories/per_cat), engine_impl.rs (dispatch → Option<IterAbsorbSpec>; singleton reads spec.right_bp; add spec to action), wpda_walker.rs (spec field + mem_attr; arm ignores spec). Gates: full G; **G4 added here as the eval BASELINE** (right/ternary via normal walker must already pass); G3 left_10000 <= 112. Falsifier: any G1/G2 fail; left_10000 > 112; G4 baseline mismatch (normal walker already wrong → root-cause first).

**S1 — Pre-fork `^` trigger (C1-R core).** Hypothesis: §3 pre-fork trigger + §4 right-nested synth_binary_chain make `2^2^…^2` absorb, parse+eval right-associated, < 500 MB (~160), fork suppressed; no regressions. Changes: wpda_walker (peek_binary_chain, synth_atom_symbol, synth_binary_chain, arm rewrite binary branch; earley_outboard_chain → dead_code), engine_impl (pre-fork trigger guard + iter_eligible_spec_dispatch). Gates: full G — G4 `^` values, G2 PowFloat eval (non-canonical/normal-walker correct), G3 right_10000 < 500 + left_10000 <= 112, G5 RIGHT panel. Falsifier: G4 `^` mismatch; "no accepting branch" (fork-suppression dropped canonical → flip to canonical-absorbs-others-normal); right_10000 >= 500; PowFloat regression; Welch LOSS.

**S2 — Pre-fork ternary trigger (C1-M core).** Hypothesis: peek_ternary_chain + mixfix-tier pre-fork trigger + synth_ternary_chain make `0?1:…:0` absorb, parse+eval 0, < 500 MB (~280); no regressions. Changes: wpda_walker (peek_ternary_chain, synth_ternary_chain, arm mixfix branch), engine_impl (extend trigger to mixfix tier; `want_pretrigger = assoc_right || is_mixfix`). Gates: full G — G4 ternary values, G2 all 8 suites (mixfix-tier change must not perturb other langs' mixfix), G3 ternary_10000 < 500 + left/right no-regression, G5. Falsifier: ternary parse fail/G4 mismatch; ternary_10000 >= 500; other-lang mixfix regression; Welch LOSS.

**S3 — Migrate AddInt onto synth_binary_chain; retire chart emit.** Hypothesis: routing AddInt through synth_binary_chain(left-nested) via the singleton site is value-equivalent + <= 112 MB, removing V7 bugs. Changes: wpda_walker (singleton-entry arm calls synth_binary_chain instead of earley_outboard_chain; head_pos recovery from GSS stack top). Gates: full G — G3 left_10000 <= 112, G4 AddInt==8 via synth, G5 LEFT panel. Falsifier: left_10000 > 112; AddInt mismatch; LEFT Welch LOSS.

**S4 — Consolidation, N>=51 Welch, pgmcp decide.** Re-run N>=51 LEFT+RIGHT panels; record 3 chain_10000 peak-RSS + samples via `experiment_record_measurement`; `experiment_decide(hypothesis_id=8)`; update ledger. Gates: full G at 51 samples; decide=accepted. Falsifier: decide rejected/inconclusive; any 10000-size >= 500.

## 6. Risk register

| # | Risk | Likelihood | Impact | Mitigation / falsifier |
|---|------|-----------|--------|------------------------|
| R1 | Fork-suppression drops a genuine alternative | Low-Med | Wrong/failed parse | Peek proves determinism; G2/G4 catch; fallback canonical-absorbs-others-normal. |
| R2 | Canonical picks wrong category | Low | Wrong eval, silent in release | Lowest src_idx = Int (V2) = AddInt pilot + lex-min EOI; G4 absorbed-vs-normal oracle. |
| R3 | Wrong rule_idx encoding | Med | Wrong cat/action | `(cat<<16)\|rule` everywhere; G4 values (release debug_assert off → G4 is the guard). |
| R4 | Op/`?`/`:` included as child → arity mismatch | Med | Corrupt args | Children = operands only (F4/F5/V6); G4+G2. |
| R5 | Atom not carrying NumLit rule | Med | Wrong eval | `spec.atom_lit_rule_idx`=per_cat[cat][0] (NumLit); G4 oracle. |
| R6 | Head-atom SPPF double-count (pop geometry) | Med | Duplicate operand | Pop exactly one head Symbol before push; G4 values + G3 RSS catch. |
| R7 | Mixfix-tier pre-fork perturbs other langs | Med | Other-lang regression | Strict right_recursive_tail + exact shape gate; runtime peek fallback; G2 all 8 suites. |
| R8 | Span collisions merge levels | Low | Corruption | Strictly-nested real positions → unique (nt,lo,hi). |
| R9 | Stack overflow at 10000 | Low | Crash | Synthesis ITERATIVE; realize iterative; AST Drop recurses → keep RUST_MIN_STACK. No emit_sppf_subforest. |
| R10 | Welch slowdown from plumbing/peek | Low | Reject | Peeks O(N) zero-alloc; absorb replaces O(N) churn. G5. |
| R11 | Incremental-build artifact masks defect | Med | False verdict | cargo clean re-confirm on surprising results. |
| R12 | Deep `2^…` i32 overflow → Int::Err | Low | G4 false negative | G4 `^` uses small exponents; the 10000 test asserts parse+RSS only (G3), not value. |

## 7. CLAUDE.md compliance
No stubs/TODOs/deferrals. `.expect("…")` over `unwrap()`; preallocate synth vectors. Welch p<0.05 (G5) every runtime substage; pgmcp #8 lifecycle is the decision record. No destructive ops; each substage `git revert`-able. `earley.rs` chart/Leo retained (17 tests); `earley_outboard_chain`+`complete_to_fixpoint` → `#[allow(dead_code)]`.

Two load-bearing facts this revision adds: **D1** — only ONE canonical category per terminal may absorb (the lex-min winner = lowest `(value_home_rank, src_idx, label)` = Int for integer terminals), else divergent cursors bypass the Tomita merge and no branch accepts; **D2** — right-assoc/mixfix never re-iterate to the singleton, so a NEW pre-fork trigger (gated on a deterministic forward peek, suppressing the spurious fork) is required at the InfixLoop binary AND mixfix tiers before the singleton-vs-fork branch.
