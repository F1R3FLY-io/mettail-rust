# Evidence-Driven Early Pruning: Design Foundation

This directory contains the evidence-pruning mechanism inventory for the pgmcp #21 design program.

## Files

### 00-existing-mechanisms-inventory.md (669 lines, 36KB)
**Complete inventory of 48+ evidence and pruning mechanisms** across the PraTTaIL/MeTTaIL WPDA parser pipeline (lex → dispatch → operand → infix → EOI → realize → eval).

**Contents:**
- Executive summary (mechanism classification by soundness & timing)
- 14 detailed sections covering each mechanism class
- Gap analysis: 5 major "evidence-available-but-fires-late" opportunities
- Summary table (pipeline stages & evidence timing)
- Appendix A (file locations for core mechanisms)

**Key findings:**
- **8 Dispatch mechanisms** (trie, FIRST/FOLLOW, visited_dispatch, etc.)
- **5 Weight/order mechanisms** (LexicographicWeight axes, Viterbi beam)
- **7 Token-soundness mechanisms** (min-span, semantic-root, EOI gates)
- **4 Cross-cat evidence mechanisms** (trigger gates, rule dispatch, into_term rejection)
- **6 Resolution gates** (premature-Accepted filter, prefix-trailing, packing)
- **4 Cycle defenses** (visited_dispatch/recovery, progress detector, CESK unwinding)
- **5 Budget/bound mechanisms** (report, never prune)
- **3 Eval-side mechanisms** (semantic_hash dedup, guard dispatch, rewrite-to-Err)
- **6 Lex-side mechanisms** (DAG soft-fail, weight edges, keyword reservation)

### 01-quick-summary.md (63 lines, 3.5KB)
**Executive summary for quick reference.** Lists the 5 biggest late-firing evidence gaps, mechanism counts by class, soundness/status matrix, and principle adherence summary.

## Evidence Classes (11 categories)

| Class                   | Mechanisms | Soundness                             | Timing Gap                                |
|-------------------------|------------|---------------------------------------|-------------------------------------------|
| Dispatch (PathMap trie) | 8          | Definite (LL(k) characterization)     | ✓ Early                                   |
| Weight/order (semiring) | 5          | Order signal (no heuristic pruning)   | Viterbi beam unused                       |
| Token-soundness (spans) | 7          | Definite (span check, EOI gates)      | min_terminal_span underused               |
| Cross-cat evidence      | 4          | Definite (type mismatch detection)    | **LATE** (semantic_root fires post-parse) |
| Resolution gates        | 6          | State/structural evidence             | **LATE** (premature-Accepted @ EOI)       |
| Cycle defenses          | 4          | Progress evidence (avoid re-visiting) | ✓ Early (342K steps saved)                |
| Budget/bounds           | 5          | Report gates (not pruning)            | ✓ Working as designed                     |
| Eval-side               | 3          | Definite/semantic                     | ✓ Implemented                             |
| Lex-side                | 6          | Definite (structural dead-ends)       | ✓ Sound                                   |
| Formal verification     | 3          | Mathematical proof                    | ✓ Zero-admission                          |

## Top 5 Late-Firing Evidence Gaps

1. **Category viability @ ProcX root (16-cursor waste)**  
   Evidence available: valid_continuations WFST + category FIRST sets  
   Opportunity: Gate at prefix dispatch via cross-cat lookahead

2. **Cast-then-infix (342,699 no-op steps)**  
   Evidence available: Cast target type (known at codegen)  
   Opportunity: Type-aware dispatch routing at cast-result position

3. **Cohort materialization (0.6% savings, weak ROI)**  
   Evidence available: ContextWeight multi-axis divergence  
   Opportunity: Lazy materialization gate (gated off, disabled, low impact)

4. **Lex-fork keyword interpretation (FIXED 2026-06-10)**  
   Evidence available: `prefix_primary_has_dispatch_rule` function  
   Opportunity: Wire into __fall_through guard  
   Status: ✓ FIXED (189/217 tests repaired, commit 51d57c91)

5. **Semantic root accepts (cross-cat cast type)**  
   Evidence available: Constructor existence (codegen-baked)  
   Opportunity: Gate earlier via semantic_root_accepts_at_cursor

## Design Principles

**User Mandate (Session 2026-06-10):**  
"Alternatives leave the live set ONLY via definite, monotone-under-continuation evidence (never heuristics). Weights ORDER, never prune. Ambiguity is first-class."

**Evidence Hierarchy:**
1. **Definite evidence** (grammar-proven): PathMap trie, FIRST/FOLLOW, type mismatch, structural dead-ends
2. **Order signals** (semiring-based): LexicographicWeight, BP tiers, lex-min extraction
3. **Progress evidence** (avoid re-visiting): visited_dispatch, visited_recovery
4. **Report gates** (call-controlled, not silent): AmbiguityBudget, MAX_STEPS, REALIZE_CAP

**Heuristics:** NOT USED. All pruning is evidence-based or report-based.

## Related pgmcp Issues

- **#21:** Evidence-driven early pruning design (this inventory is foundation)
- **#280-294:** Phase M-RHO (Rholang bridge)
- **#307:** 342,699 no-op steps (cast-then-infix gap)

## Next Step: Phase 5A Implementation

**Design documents:** `evidence-driven-early-pruning.md` (dcc253b9), `CastDelegateMergeBound.v` (629e9759)

**Approach:** Lookahead-gated cross-cat delegate dispatch
- Evidence gate: FIRST(infix trigger) lookahead + type-usage/sink-type
- No-loss frontier shrink (covers K^d candidates)
- Lazy gate via cohort-shared dispatch + cursor-merge bounds

**Formal verification:** Zero-admission proofs of soundness

