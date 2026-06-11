# Evidence-Driven Pruning: Quick Summary

**48+ Evidence Mechanisms Inventoried** across 11 mechanism classes.

## Biggest Late-Firing Evidence Gaps

1. **Category viability @ ProcX (16-cursor waste)**  
   Evidence: WFST valid_continuations + category FIRST  
   Fires LATE: Premature-Accepted filter (EOI)  
   Fires EARLY: Could gate at prefix dispatch via cross-cat lookahead
   
2. **Cast-then-infix 342,699 no-op steps**  
   Evidence: Cast target type (known at codegen)  
   Fires LATE: Infix loop tried for all source-cat rules  
   Fires EARLY: Could switch dispatch category at cast-result via type-aware routing
   
3. **Cohort materialization without ContextWeight gate**  
   Evidence: Multi-axis divergence metric computed but unused  
   Fires LATE: Never (H1 gated off)  
   Fires EARLY: Could lazily materialize members only if ≥2 axes diverge (weak ROI: ~0.6%)
   
4. **Lex-fork keyword interpretation (FIXED 2026-06-10)**  
   Evidence: `prefix_primary_has_dispatch_rule` function existed  
   Fires LATE: __fall_through only  
   Fires EARLY: Wired into guard (51d57c91), fixed 189/217 fails
   
5. **Semantic root accepts (cross-cat cast type)**  
   Evidence: Constructor exists for target category  
   Fires LATE: During realization (post-parse)  
   Fires EARLY: Could gate at cross-cat dispatch (semantic_root_accepts_at_cursor)

## Mechanism Count by Class

| Class | Count | Soundness | Status |
|-------|-------|-----------|--------|
| Dispatch (FIRST/FOLLOW trie) | 8 | Definite | ✓ Early |
| Weight/order (semiring) | 5 | Order signal | ✓ Working |
| Token-soundness (spans) | 7 | Definite | ✓ Implemented |
| Cross-cat evidence | 4 | Definite | **GAP** (late) |
| Resolution gates | 6 | State/definite | **GAP** (premature-Accepted) |
| Cycle defenses | 4 | Progress | ✓ Early |
| Budget/bounds (report) | 5 | Safety gate | ✓ Working |
| Eval-side | 3 | Definite/semantic | ✓ Implemented |
| Lex-side (DAG/soft-fail) | 6 | Definite | ✓ Implemented |
| Formal verification | 3 | Proof | ✓ Zero-admission |

## Principle Adherence: "Definite Evidence, Never Heuristics"

✓ **Core mechanisms follow the mandate:** PathMap trie (definite FIRST/FOLLOW), visited_dispatch (progress), lex soft-fail (structural dead-ends), formal verification (zero-admission proofs).

✓ **Weights order, never prune:** LexicographicWeight is a semiring; Viterbi extraction is sound. No silent dropping.

✓ **Ambiguity is first-class:** AmbiguityBudget gates report overflow, don't prune. semantic_hash dedup preserves observational distinctions (-3! bug was Display-dedup loss, fixed by switching to semantic_hash).

✓ **Budget mechanisms report, don't prune:** MAX_STEPS, AmbiguityBudget, REALIZE_CAP all surface structured errors; caller decides response.

## Design Debt

1. **Phase 5A (cast-delegate routing):** Models pending user mandate "work backwards from FV." CastDelegateMergeBound.v and evidence-driven-early-pruning.md design doc define the approach. Needs implementation of lookahead-gated cross-cat dispatch.

2. **ContextWeight H1:** Disabled after empirical measurement showed weak ROI (0.6% would-merge at chain_50 with gate ≥60%). Diagnostic instrumentation retained.

3. **Viterbi prediction beam:** Fully implemented but disconnected from dispatch path. Could be wired to reorder (not prune) ambiguous dispatch candidates by predicted best-first.

---

**Full Inventory:** See `00-existing-mechanisms-inventory.md` (669 lines, 11 sections, 48+ mechanisms, 5 gap analyses, file/location reference table).
