# Float Cast-Family Root — FLIP-PROVEN (2026-06-02)

After M6–M9 + the InflightCollision (flip-refuted) + the GLL cycle-defense (refuted by identical fire counts), the actual bedrock root of `float(float(10,64),64)` / `test_nested_float_float_int` / `test_triple_nested_float` failing is **FLIP-PROVEN** (agent `a304ec4e`, 2026-06-02).

## ROOT (flip-confirmed)
The inner `float(` dispatch in Float context (`state_cat_src_idx == 5`) is a 5-way `Fork` over the five `"float"`-triggered rules (`classify_binder` accepts all five because each has `sp[0] == Literal("float")`):
- `IntToFloat` (rule_idx 11), `BoolToFloat` (12), `StrToFloat` (13), `FloatId` (14) — the four single-arg **unary casts** (`tc.len()==1`).
- `FloatBin` (15) — the 2-arg **fold** `a:Proc, w:Int |- "float" "(" a "," w ")"`.

All five branches are emitted at the **identical lex weight `lex_w(0.0, 5, rule_idx)`** — same `primary` (0.0), same `src_idx` (5 = Float; the binder-group Fork keys on the **result** category, not the source). The lex-min tiebreak order is `(primary, lex_alt_idx, src_idx, rule_idx)` (`prattail/src/automata/lex_weight.rs`); with the first three components TIED, disambiguation **collapses to `rule_idx` ascending** → the four unary rules (11–14) all outrank `FloatBin` (15, dead last). So under an outer `float(` the inner `float(` **commits to a unary reading purely by declaration order, BEFORE the `,`/`)` token evidence can distinguish the fold** → `FloatBin` never parses → the inner float never resolves → the outer `FloatBin`'s `a:Proc` slot never fills → "no accepting branch reached end of input."

**This is a PREMATURE-DISAMBIGUATION bug:** the fold alternate is dropped by an arbitrary `rule_idx` tiebreak, NOT by evidence — a direct violation of the WPDA invariant (never drop a parse alternate until the evidence rejects it).

## FLIP PROOF (the bedrock test, not a hypothesis)
`FLIP_NOUNARY=1` (gate OUT the 4 unary-cast branches from the binder-group Fork emission in `macros/src/gen/runtime/wpda_codegen/binder.rs` ~`:1140-1177`, leaving only `FloatBin`):
| Input | baseline (flip OFF) | FLIP_NOUNARY=1 |
|---|---|---|
| `float(float(10,64),64)` | ERR | **PARSE-OK** (nf 10.0) |
| `float(int(5,32),64)` | ERR | **PARSE-OK** (5.0) |
| `int(int(5,32),32)` | OK | OK (5) |
| `float(uint(5,32),64)` | OK | OK (5.0) |
| `float(10,64)` | OK | OK (10.0) |

Gauntlet `prattail --lib` 4220/0; one 32G-capped build. Removing the starving unary branches flips float FAIL→PASS while every control holds ⇒ ROOT CONFIRMED. (With the flip, the regenerated `target/generated/calculator/wpda.rs:1117-1136` arm collapses from a `Fork` to a single `ConsumeAndPush` straight into `FloatBin`'s `BinderRule` worker, and the nested parse succeeds.)

## Why `int(int)` passes at baseline
Int carries cross-cat projection redundancy (`FloatToInt` etc. + bare-Integer projections) giving `IntBin` an alternate, non-Fork-starved path that Float lacks — consistent with every prior finding (the "Int redundancy" thread that ran through M9).

## Generality
ALL keyword trigger groups that mix single-arg casts + a multi-arg fold are affected: `float`/`int`/`uint`/`fixed`. `int`/`uint`/`fixed` only LOOK fine (redundancy / operand shape). The fix MUST be symmetric — at the binder-group Fork emission / lex-min tiebreak — NOT float-specific.

## What a real (generalized, principled) fix must do
Disambiguate the trigger-group Fork so the multi-arg fold **survives** rather than being out-ranked by the unary casts on a bare `rule_idx` tiebreak — decided by **EVIDENCE** (the post-trigger token shape: a second `,`-separated argument before `)`), NOT declaration order. Per the HARD INVARIANT: keep BOTH the unary and fold alternates alive until the `,`/`)` lookahead resolves which one (do NOT pre-commit by `rule_idx`). The realize-time `min_terminal_span` filter already rejects token-unsound cast fabrications; the gap is purely the premature `rule_idx` commit before the `,` evidence arrives. Candidate mechanisms (to be Plan-confirmed): (a) keep same-`(primary,src_idx)` Fork branches co-equal (don't fold the `rule_idx` tiebreak into a hard pick) so the cursor explores both until the `,`/`)` token prunes; (b) give the fold branch a strictly-winning weight only when its distinguishing `,` is present in lookahead. (a) is the more invariant-aligned (evidence-driven, no weight heuristic).

**Sites:** `macros/src/gen/runtime/wpda_codegen/binder.rs` ~`:1140-1177` (binder-group Fork emission + `classify_binder`); `prattail/src/automata/lex_weight.rs` (the `(primary, lex_alt_idx, src_idx, rule_idx)` lex-min order). Must preserve: standalone unary casts (`float(10.5)`, `int(true)`, …), the Bool win (`:2188`), the 3 M3.1-sentinels, `test_nested_float_int_arithmetic`, chain Welch, op-suites, gauntlet 4220/0.
