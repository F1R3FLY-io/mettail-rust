# Dovetail Creusot Budget Contract

This crate contains the Rust-level Creusot contract model for Dovetail budget
admission. It verifies the scalar budget boundary used by the e-graph and
rules-as-data saturation path:

- `try_add_with_budget` either adds exactly one node below the budget or reports
  overflow at the unchanged used count;
- `added_never_overshoots_budget`;
- `overflow_preserves_state_at_limit`;
- `add_succeeds_below_limit`.
- `admit_enode_with_budget` mirrors Dovetail's fresh-vs-existing admission
  boundary, including the sticky node-limit flag;
- `admission_never_overshoots_budget`;
- `existing_enode_preserves_budget_state`;
- `fresh_enode_below_limit_adds_once`;
- `fresh_enode_at_limit_sets_node_limit`.

The formal harness runs this crate with Creusot's pinned Rust toolchain
(`nightly-2026-04-21`), generates Coma, and proves the resulting verification
conditions with `why3find`.

The local Creusot/Why3 installation has two compatibility wrinkles that the
harness handles under `.formal-tmp`:

- `cargo-creusot` emits a newer `why3find --summary` flag than the installed
  `why3find 1.3.0` accepts, so the harness invokes `why3find prove` directly
  with equivalent supported options;
- the generated Creusot prelude needs small signed-integer compatibility
  constants for this Why3 stack, patched only in the copied `.formal-tmp`
  package, never in the installed Creusot checkout.

The hashmap-backed e-graph and extractor internals are covered by Rocq models
plus Rust trace/audit tests. This Creusot crate covers the Rust-level scalar
budget contract those components call through.
