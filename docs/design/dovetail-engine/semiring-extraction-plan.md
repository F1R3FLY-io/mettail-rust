# dovetail-semiring extraction plan (Increment 1)

> Plan-agent design (2026-06-09). Extract the weight algebra from
> `prattail/src/automata/semiring.rs` (6502 lines) + `lex_weight.rs` (905) into a
> NEW lower crate `dovetail-semiring`; `prattail` re-exports it (single source of
> truth) and stays green. Rollback anchor: the clean HEAD captured at start.

## Key de-risking finding
The `super::super::*` test imports live in **nested** submodules inside
`#[cfg(test)] mod tests`; a whole-file `git mv` preserves module nesting, so they
**resolve unchanged** — zero edits. Only **3 absolute `crate::…` test imports**
break. Production coupling = `PackingFactored<W>` (3 sigs + 2 doc links) only.
FV: `SemiringLaws.v` proves provenance/relational/kat, NOT these weights — only a
stale traceability comment to update.

## Decisions
- **D1** `git mv` both files (preserves blame/history); prattail gets glob-re-export facades.
- **D2** Tests MOVE with the algebra (nesting preserves `super::*`); add `proptest` dev-dep to dovetail-semiring.
- **D3** `lex_weight.rs` moves too (semiring tests reference `LexicographicWeight`; orphan rule keeps trait+impl together).
- **D4** All-or-nothing: every trait + weight + Newton fn + `PackingFactored` → dovetail-semiring. `provenance`/`relational`/`kat`/`newton.rs` STAY in prattail.
- **D5** deps: `num-complex` (for `AmplitudeWeight`), dev `proptest`. No `[features]` unless a moved `cfg(feature=…)` test demands it (verify).
- **D6** FV: comment-only edit in `SemiringLaws.v`.

## Execution (gate after each landable unit; commit Units 1+2 atomically only when green)
**Unit 1 — create the self-contained crate (workspace intentionally breaks until Unit 2):**
1. `dovetail-semiring/Cargo.toml` (num-complex dep, proptest dev-dep); add `"dovetail-semiring"` to workspace members.
2. `git mv prattail/src/automata/semiring.rs dovetail-semiring/src/lib.rs`; `git mv …/lex_weight.rs dovetail-semiring/src/lex_weight.rs`.
3. Top of lib.rs: `pub mod lex_weight; pub use lex_weight::LexicographicWeight;`.
4. lex_weight.rs import `use crate::automata::semiring::{…}` → `use crate::{…}`.
5. Relocate `PackingFactored<W>` from `sppf.rs` into lib.rs (just before `solve_scc_weights_newton`); rewrite the 3 sigs `crate::sppf::PackingFactored` → `PackingFactored` + the 2 doc links.
6. Fix the 3 absolute test imports (`crate::automata::lex_weight::LexicographicWeight` → `crate::lex_weight::LexicographicWeight` ×2; `crate::sppf::PackingFactored` → `crate::PackingFactored` ×1).
7. Verify no moved `cfg(feature=…)` needs a feature stanza.
- GATE 1: `cargo build -p dovetail-semiring --all-targets` + `cargo test -p dovetail-semiring --lib` green (record moved test count `$MOVED`). Workspace build EXPECTED to fail until Unit 2.

**Unit 2 — prattail facade (restores workspace GREEN):**
1. `prattail/Cargo.toml`: add `dovetail-semiring = { path = "../dovetail-semiring" }`.
2. New `prattail/src/automata/semiring.rs` = `pub use dovetail_semiring::*;`.
3. New `prattail/src/automata/lex_weight.rs` = `pub use dovetail_semiring::lex_weight::*;`.
4. `sppf.rs` where `PackingFactored` was: `pub use dovetail_semiring::PackingFactored;`.
- GATE 2: `cargo build --workspace --all-targets` clean; **`prattail-lib + dovetail-semiring-lib == 4350, 0 failures both`** (tests physically moved, so prattail-lib drops by `$MOVED`; combined == 4350/0); op-suite failing-set == 28d4d26 baseline (≤217, identical set).

**Unit 3 — FV/doc hygiene (independent):** update the stale `SemiringLaws.v` traceability comment; `make -C formal check-capped` green.

## Riskiest step
PackingFactored relocation + the `sppf.rs` `pub use` re-export (Step 2.4) — if the re-export is omitted, `wpda_walker.rs:5632` (the production extraction path the op-suite guards) fails to resolve. Do the relocation + re-export as a paired change; let GATE 2's workspace build arbitrate.

## Rollback (uncommitted)
`git checkout -- .` ; `git clean -fd dovetail-semiring/` ; `git checkout $ANCHOR -- prattail/src/automata/semiring.rs prattail/src/automata/lex_weight.rs` ; confirm `cargo test -p mettail-prattail --lib` recovers.
