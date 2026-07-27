# Phase F: cursor.builder Deletion — Design

**Date**: 2026-05-17
**Branch**: `feature/wfst-architecture`
**Status**: design ready for user review (NO code modifications until approved)
**Replaces / extends**: `~/.claude/plans/c9-cleanup-options-comparison.md`,
`~/.claude/plans/revised-master-plan.md` §Phase F estimate

---

## Investigation Findings

### Read-site enumeration (corrected)

The original master-plan count of "10 read sites" overestimates. The actual
non-comment, non-`self.builder` `cursor.builder` reads are **7 logical
sites** (some duplicated as read-pairs):

| Line | Site | Use |
|------|------|-----|
| 2206 | `current_snapshot` (tracing/hang-dump) | `c.builder.collection_stack_len()` for diagnostic dump |
| 2807, 3937 | `resolve_at_end_of_input` det-arm install + `apply_action` Alive/Resolved install | `self.builder = (*cursor.builder).clone()` |
| 2996 | `resolve_at_end_of_input` nondeterministic-multi arm | `(*self.branch_cursors[idx].builder).clone()` then `take_dyn_result` |
| 3686 | `is_accepting_config` | `cursor.builder.is_accepting_terminal()` (EOI gate) |
| 6059, 6105–06 | `merge_equivalent_cursors` ConfigKey | `collection_stack_len()` (hash key + debug_assert) |
| 6933 | `emit_fire_action` debug_assert | `cursor.builder.len()` |
| 7293, 7554 | `set_cursor_inner_state` HashMap kv_phase + acc_id derivation | `collection_slot_len()` + `collection_stack_len()` |
| 7665, 7707 | D8 / GroupingClosePreservingInner | `top_term_type_name()` |

### Realize path is independent

`realize_packing_call` (line 3491) uses a FRESH `SemanticBuilder`.
cursor.builder is not consumed by realization — only by the legacy
`take_dyn_result` install path that already has SPPF root +
`realize_root_to_terms` fallbacks at lines 2963–2968.

### Writes

- 14 `Arc::make_mut(&mut cursor.builder).<m>()` sites in `emit_*` helpers.
- 11 `Arc::clone(&cursor.builder)` Fork-fanout sites.
- 4 `Arc::new(SemanticBuilder::new())` reset sites.

Every write is **structurally redundant** with the parallel
`sppf_stack` / `sppf_collection_arena` / `binder_scope_marks` mutation.

### Key invariant

The cursor maintains by construction:

```text
cursor.builder.len() ≡ cursor.sppf_stack.len() - cursor.optional_scope_marks.last().unwrap_or(0)
```

When no optional scope is open these are equal; both grow/shrink by the
same delta on every emit helper. Same goes for `collection_stack_len()`
matching `sppf_collection_arena[...]`-allocated-count.

---

## Read → SPPF Mapping

- **`is_accepting_terminal()`** →
  ```rust
  cursor.optional_scope_marks.is_empty()
      && matches!(cursor.sppf_stack.as_slice(),
                  [] | [sid] if sppf.node(sid) == Some(Symbol{..}))
  ```
  The "single Symbol" Phase-C invariant replaces "single Term" (Packing
  yields a Symbol id on `emit_fire_action`).

- **`collection_stack_len()`** does NOT have a 1:1 sppf-only equivalent
  because `sppf_collection_arena` is APPEND-ONLY and never shrinks. The
  authoritative count of OPEN slots requires a **new field**.
  **Recommended replacement**: add `cursor.collection_stack_depth: u8`,
  increment in `emit_start_collection`, decrement in
  `apply_pop_body_to_cursor` at the existing CollectionMarker pop site.

- **`collection_slot_len(acc_id)`** → `sppf_collection_arena[acc_id].len()`
  (the arena IS the slot — they grow in lockstep via
  `emit_splice_into_collection`).

- **`len()` at 6933** → already redundant with the preceding
  `cursor.sppf_stack.len() >= arity` guard; either delete or replace inner
  expr with `cursor.sppf_stack.len()`.

- **`top_term_type_name()`** (7665, 7707) →
  ```rust
  cursor.sppf_stack.last().and_then(|sid| match sppf.node(sid) {
      Some(Symbol{non_terminal_tag, ..}) => Some(*non_terminal_tag as u16),
      _ => None,
  })
  ```
  Skips the `cat_of_type_name` string round-trip — strictly simpler & faster.

- **`take_dyn_result`** (2807, 2956, 2996): replace by extracting via
  `realize_root_to_terms(winner_sppf_root, Some(1))[0]` — the SPPF root
  is already captured at lines 2810–14, 2950–54, 2989–94. The fallback
  at 2963–68 (Accepted with empty terms but valid root) already takes
  this path; we just promote it to primary.

---

## Migration Strategy: STAGED (5 steps, each separately gated)

More invasive than the master plan suggested. Staged is essential.

### F.0 (~−15 LoC)

Replace `take_dyn_result` install at 2807, 2956, 2996 with
`realize_root_to_terms` reads of `det_sppf_root` / `winner_sppf_root` /
per-cursor `cursor_root`. Self.builder reads outside the install path
remain (accessors at 2356–2364 are public API used by codegen facades —
leave them, they have empty builders post-migration). **Gate full
gauntlet.**

### F.1 (~+10 LoC, 0 LoC delete)

Introduce 5 helpers operating on cursor + sppf + sppf_collection_arena:
- `is_cursor_accepting_terminal`
- `cursor_top_non_terminal_tag`
- `cursor_collection_slot_len`
- plus a new field `cursor.collection_stack_depth` initialized at 0 in
  all 4 cursor-construction sites.

Wire `emit_start_collection` to increment and add a single decrement at
the CollectionMarker pop site in `apply_pop_body_to_cursor`. **Gate
gauntlet** — this stage adds, does not replace.

### F.2 (~+30 LoC at callsites)

Replace all 7 read callsites with helper calls. Keep cursor.builder
writes intact. **Gate gauntlet** — divergence between SPPF-derived
helpers and cursor.builder reads will surface here.

### F.3 (~−400 LoC)

Delete:
- 14 `Arc::make_mut(&mut cursor.builder)` lines
- 11 `Arc::clone(&cursor.builder)` fields
- 4 `Arc::new(SemanticBuilder::new())` field inits
- 1 `Arc::strong_count` in Debug impl
- the field declaration + docstring at 1066–92
- 1 unit-test reference at ~8950

Update `fork_child` / `seed_from_live`. **Gate gauntlet.**

### F.4

Audit `self.builder` — likely orphaned by F.0 except for the public
accessors. If unused by codegen facades, delete in a separate follow-up.

---

## Risk Register

- **PRIMARY**: Step F.1's `collection_stack_depth` decrement-on-pop must
  hit exactly the same sites where `cursor.builder.collection_stack` would
  drain. The runtime SemanticBuilder drains via `drain_collection(id)`
  invoked INSIDE action_fn (codegen-emitted) — visible to walker only via
  `collection_stack_len()` shrinking. The walker-side counterpart is
  harder to synchronize.
  **Mitigation**: instrument the helper to count Class-3/Class-5 distinct
  paths during F.2 and verify against `cursor.builder.collection_stack_len()`
  via a debug_assert before deleting the field.

- **SECONDARY**: ConfigKey hash key change (line 6059) — any drift
  collapses cursors that shouldn't merge or splits cursors that should.
  **Mitigation**: a parity test
  `cursor.builder.collection_stack_len() == cursor.collection_stack_depth`
  at every `merge_equivalent_cursors` entry.

- **TEST GAUNTLET**: prattail lib (4029 tests), macros, calc_op (1321),
  rholang_op (532), edge_case_tests (223), recovery_integration_tests
  (test_calc_recovery_trailing_* exercise EOI/optional/recovery
  interactions heavily), optional_group_smoke (kept the L4 dangling-else
  invariants alive), wpda_trace_dump (snapshot consumers). HashMap-
  collection tests (Class-3 binder list) and multi-binder Class-2
  (`Pair . xs, ys`) are the highest-signal regressions for the
  collection-depth back-port.

---

## LoC Delta (honest)

| Stage | LoC delta |
|-------|-----------|
| F.0 | ~−15 net |
| F.1 | ~+50 (4 cursor-init sites × ~3 LoC + 5 helpers × ~5 LoC + decrement at 1 site + Debug field) |
| F.2 | ~+30 at callsites |
| F.3 | ~−480 (14 writes + 11 Arc::clones + 4 Arc::news + 1 field + ~14 LoC of inline rationale comments) |
| **Net** | **~−415 LoC** — matches master plan's −420 estimate |

---

## Mandate Compliance (P1/P2/P3)

- **P1 preserve-all-derivations**: untouched. SPPF Symbol-dedup at
  `(nt, lo, hi)` continues to be the ambiguity substrate; deletion is
  structural cleanup, no decision logic changes.
- **P2 rule-out-by-evidence**: untouched. The Premature-Accepted filter
  (Phase E Fix A) operates on `c.pos` and `c.inner_state`, not
  `cursor.builder`.
- **P3 semiring-correct ⊕ at merge**: ConfigKey's `collection_depth`
  discriminator preserved via the new cursor field — same hash semantics,
  same merge behavior.

---

## Honest Trade-offs

### Gains

- ~415 LoC deletion
- Structural elimination of the dual-mode-mirror bug class
- Faster Fork fanout (no `Arc::clone(&builder)` per child × 11 sites —
  replaced by inheriting cursor.sppf_stack + cursor.collection_stack_depth:
  u8 by-value copy, which is structurally smaller)
- The cross-cat-resolution string round-trip via `cat_of_type_name`
  becomes a direct SppfNode::Symbol read

### Losses

- An additional `u8`-sized cursor field
- The Debug impl loses the `Arc::strong_count` diagnostic
- Hang-dump's `collection_depth` becomes the new field rather than the
  builder mirror — semantically equivalent

### Calibrated estimate

**6–10 hours** including running the gauntlet at each gate. Higher than
the master plan's 4–6 estimate because Step F.1's `collection_stack_depth`
mirror is genuinely tricky to wire correctly — it's the one place where
the master plan's "structurally redundant" framing breaks down.
