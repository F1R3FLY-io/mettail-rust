# Dovetail Creusot Pilot

This crate contains the Rust-level Creusot pilot for Dovetail formal
verification. It verifies the budget-admission contract used by the e-graph and
rules-as-data saturation boundary:

- `try_add_with_budget` either adds exactly one node below the budget or reports
  overflow at the unchanged used count;
- `added_never_overshoots_budget`;
- `overflow_preserves_state_at_limit`;
- `add_succeeds_below_limit`.

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

Do not start by targeting the hashmap-heavy e-graph or extractor internals.
Those stay covered by Rocq models plus Rust trace/audit tests until a focused
Rust-verification subset is carved out.
