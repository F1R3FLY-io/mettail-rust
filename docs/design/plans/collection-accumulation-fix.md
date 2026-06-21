# Collection-Accumulation Fix (Clusters A + C + E) — 2026-05-29

Resolves 20 broad-suite failures from ONE root cause. Designed via Plan agent with empirical
tracing (`PRATTAIL_TRACE=cursors`). Part of `docs/design/plans/drive-suite-green-ledger.md`.

## Root cause (corrected from initial hypothesis)
NOT parse-time under-accumulation — splices fire for **every** element (verified: `map(1:10,2:20)`
drives `sppf_collection_arena[0]` to len=4; `(x?y)` splices `ns` via `AdvanceWithEffect{SpliceIntoCollection}`).
The defect is **realize-time cursor mis-attribution**:
- Collection elements live in a per-cursor side-table `BranchCursor::sppf_collection_arena: Arc<Vec<Vec<SppfId>>>`
  (`wpda_walker.rs:1597`), OUTSIDE the SPPF.
- The SPPF node carries only the slot index: `SppfNode::CollectionId { id: u32 }` (`sppf.rs:222`), and is
  **dedup'd by `id`** (`sppf.rs:575`), so all derivations referencing slot `id` share one placeholder; `Packing`
  dedup `(rule_idx, children)` then collapses derivations whose collections differ but whose `CollectionId{id}`
  child is identical.
- Parse-time fire reads the OWNING cursor's arena (`fire_action_via_transient:11136` — correct). **Realize** reads
  `winner_collection_arena()` = `branch_cursors[0]` (`realize` DFS `:4384`, `realize_packing_call :4899`,
  accessor `:10923`) — usually NOT the cursor whose derivation is being realized → truncated/empty collection.
- Symptoms: map keeps the LAST pair (committed winner's arena holds a subset); PInputs `ns` empties → comm
  `multi_substitute_name([x],[])` → `subst.rs:6747` OOB. List literals pass by accident (single dominant cursor
  becomes `branch_cursors[0]`). Single-binder rhocalc fails / multi-binder passes due to dedup+terminal-check interaction.

## Fix (one fix, 3 files) — make collection elements derivation-local in the SPPF
- **Change A — `prattail/src/sppf.rs`:** `CollectionId { id: u32, items: Vec<SppfId> }`; `intern_collection_id(id, items)`;
  **remove `dedup_collection_id`** (distinct items → distinct nodes; Packing dedup still merges truly-identical
  derivations and now correctly separates differing ones). Update leaf-classifier match arms (`~:826/:861/:1023`,
  still leaf — realize DFS walks `items`, not the SPPF).
- **Change B — capture at fire site (`wpda_walker.rs` `emit_fire_action:11339→:11410`, `fire_action_via_transient`):**
  before `intern_packing`, map each `CollectionId{id}` child → re-intern with snapshot
  `cursor.sppf_collection_arena.get(id).cloned().unwrap_or_default()`. Loop over ALL children (multi-slot rules).
  `emit_push_collection_id` may keep interning an empty-items placeholder for the structural `sppf_stack` push.
- **Change C — realize reads structural `items`, not `branch_cursors[0]`:** DFS arm `:4384` iterates the node's own
  `items`; `realize_packing_call :4886-4917` reconstructs from the matching `CollectionId` child node's `items`
  (thread child SppfId/items in; reuse existing `memo`→`push_term_arc`+`push_to_collection`); slot pre-alloc
  `:4870-4874` + `push_collection_id` `:4917` unchanged. Then **delete dead `winner_collection_arena()` `:10923`**
  (genuine removal — only callers migrated — with one-line rationale).

## Invariants
- Disambiguation PRESERVED: only changes single-derivation element storage; `resolve_at_end_of_input` accepting-set
  + `Ambiguous([...])` untouched. Strengthens (not relaxes) dedup — distinct collections become distinct nodes.
- `drain_collection` LIFO `debug_assert` (`wpda_runtime.rs:2434`) now HOLDS (per-derivation items → deterministic
  single-slot lifecycle); do NOT weaken it.
- Parse-time machinery (splice gate `:13155`, Class-3 `SpliceIntoCollection`, kv_phase `:11853`) untouched.

## Verify
gauntlet `cargo test --release -p prattail --lib` (4206/0; update SPPF-shape unit tests to new node shape);
op-suites (gen_calculator_op ≥1321, gen_rhocalc_op 532/0); 20 targets (comm::*, new_and_extrusion::*,
parsing::multi_input/receive/new_single, rhocalc_cast_under_send_reduces_via_comm; test_map_get/keys/values/merge +
map-NF); class2/3 + wpda_parity collection smokes; Welch panel (release, quiet, N≥15).

## Risks
Class-2/3 multi-slot rules (loop over each CollectionId child); Packing-dedup node-count growth on ambiguous
collections (bounded by AmbiguityBudget; Packing dedup still collapses identical); confirm no other
`winner_collection_arena` caller before deletion (grep: only `:4384`,`:4899`).
