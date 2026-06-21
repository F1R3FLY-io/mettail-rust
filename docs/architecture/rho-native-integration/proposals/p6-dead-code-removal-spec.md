# P6 Dead-Code Removal Spec — `macros` (logic/ Ascent-source pipeline)

**Status: EXECUTED** — the `logic/` Ascent-source pipeline and its dead transitive closure were removed in P6 Stage 1 (`9d889894`). Retained as the removal record.

Computed by a code-grounded Plan agent (2026-06-16) after the Ascent **engine
generation** was excised from `macros/src/gen/runtime/language.rs`,
`compose_gen.rs`, and `test_gen/`. With `generate_ascent_source` no longer
called, its entire transitive closure (229 inventory items + dead impl/`#[cfg(test)]`
blocks) is unreachable. Goal: `cargo check -p macros --all-targets` → 0/0.

Inventory: `/tmp/p6-dead-inventory.txt` (229 rows). First check: `/tmp/p6-macros-check-1.txt`.

## Disposition (all 229 accounted)

| File | Disposition |
|---|---|
| `logic/antipattern.rs` | DELETE FILE |
| `logic/categories.rs` | DELETE FILE |
| `logic/congruence.rs` | DELETE FILE |
| `logic/helpers.rs` | DELETE FILE |
| `logic/pattern_codec.rs` | DELETE FILE |
| `logic/relations.rs` | DELETE FILE |
| `logic/bloom_filter.rs` | DELETE FILE (struct+impl+tests all dead) |
| `logic/equations.rs` | DELETE FILE (2 `impl Display` + tests also dead) |
| `logic/fusion.rs` | DELETE FILE (`FusionCandidate`/`FusionReport`+tests only used by dead) |
| `logic/pattern_trie.rs` | DELETE FILE (all impls/`unsafe impl`s + tests dead) |
| `logic/mod.rs` | SURGICAL — keep header + cleaned mod/use block only |
| `logic/common.rs` | SURGICAL — keep `compute_hol_domain_pairs`, `extract_arrow_types`, `scan_tokens_for_hol_refs` |
| `logic/rules.rs` | SURGICAL — keep `generate_freshness_functions` |
| `logic/writer.rs` | SURGICAL — delete `write_ascent_file` only |
| `gen/runtime/guard_codegen.rs` | SURGICAL — keep tristate/codegen/SFA/register/awa |
| `gen/native/rust_code_rewrite.rs` | SURGICAL — delete `safeify_methods_and_wrap` + `MethodOnlySafeifier` |
| `logic/multi_channel_analysis.rs`, `logic/stratification.rs` | FULLY KEPT |

## Kept surface
`writer::spill_and_include`, `common::compute_hol_domain_pairs`,
`rules::generate_freshness_functions`, `stratification::analyze`,
`multi_channel_analysis::*`. **Correction (agent F1):** `common::compute_core_categories`
is DEAD (sole caller was `generate_ascent_source`), not kept — it is deleted.

## Execution notes (agent flags)
- **F2:** `#[cfg(test)] mod tests` in `mod.rs`/`common.rs`/`rules.rs`/`guard_codegen.rs`
  exercise deleted fns → must be deleted to keep `cargo test`/`--all-targets` green
  (plain `cargo check` is unaffected). We delete them (test-clean).
- **F3:** `common.rs`/`rules.rs` surviving `use` lists are heuristic — drive the final
  list with `cargo check` `unused_imports`, remove-then-readd.
- **F4/F5:** confirm `writer.rs` EOF line + `rules.rs` 1489–1524 second cfg-test fn close
  before deleting.
- **Bookkeeping:** drop 10 `mod` decls + all `pub use` re-exports in `mod.rs`; delete
  `gen/runtime/language.rs:8 use crate::logic::list_all_relations_for_extraction;`.

Full ordered ranges are executed live with per-file `cargo check` gating; this file
records the disposition + rationale (the ranges shift as edits land, so they are not
frozen here — the gate is the compiler).
