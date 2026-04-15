# CEK-4: WPDS-Informed Dead Frame Elimination

## Intuition

WPDS poststar analysis proves which stack configurations are reachable from the initial configuration. Some frame variants may correspond to WPDS stack symbols that have zero weight in the P-automaton — they are provably unreachable. We can suppress their codegen entirely.

## Algorithm

1. Build WPDS with `BooleanWeight` (reachability analysis)
2. Run `poststar()` to compute the saturated P-automaton
3. For each frame variant, look up its corresponding `StackSymbol` via the CEK-3 bijection
4. Query `is_symbol_accepted(symbol)` on the P-automaton
5. If the symbol is NOT accepted → mark the frame variant as dead
6. In codegen:
   - `write_frame_enum()`: skip dead variants
   - `write_unwind_handlers()`: skip dead match arms
   - `write_prefix_phase()`: skip arms that would push dead frames

## Soundness

**Theorem (Dead Rule Soundness / CEK.3):** Zero-weight symbols in poststar correspond to unreachable rules in any concrete parse.

*Proof.* By contraposition of the Forward Simulation theorem (CEK.2): if a frame were ever pushed in a concrete parse, the WPDS simulation guarantees a corresponding transition, which would give the symbol non-zero weight. Therefore, zero weight implies never pushed. ∎

## Implementation

### Files Modified

| File | Change |
|------|--------|
| `trampoline.rs` | `write_frame_enum()`, `write_prefix_phase()`, `write_unwind_handlers()`: filter by liveness |
| `pipeline.rs` | Pass dead-frame set through `TrampolineConfig` |
| `cost_benefit.rs` | `Optimization::DeadFrameElimination`, gate `dead_frame_elimination` |
| `lint.rs` | `lint_cek03_unreachable_frame_variant()` |

### Optimization Gate

- **Code:** `CEK03`
- **Name:** `DeadFrameElimination`
- **Speedup:** 0.2 (eliminates dead code from generated parser)
- **Cost:** 0.15 (requires WPDS construction + poststar + bijection)
- **Applicability:** When grammar has ≥ 2 categories (cross-category analysis)

### Lint

- **Code:** `CEK03`
- **Name:** `unreachable-frame-variant`
- **Severity:** Note
- **Message:** Reports frame variants proven unreachable by WPDS analysis

## Enhanced Analysis via Parity Tree Automata

Beyond WPDS poststar, parity tree automata (`parity_tree.rs`) can identify frames that are dead due to structural properties of the AST:

1. Build a parity alternating tree automaton over the frame dependency graph
2. Check: "does any accepting run visit frame X?"
3. This is more precise than WPDS for tree-structured properties

## Enhanced Analysis via Petri Net Concurrent Reachability

For grammars with cross-category calls that create concurrent-like patterns, Petri net analysis (`petri.rs`) can identify frames dead due to cross-category interference:

1. Model each category as a place, each cross-category call as a transition
2. Check coverability of the frame's place in the context of all other categories
3. Identifies dead frames that WPDS misses due to its single-control-location abstraction
