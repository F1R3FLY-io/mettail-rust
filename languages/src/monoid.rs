//! GSLT omnibus conformance — **L2 `Monoid`** (`omnibus.tex:430-449`), rung two
//! (types + terms + **equations**; `rewrites { }` is empty).
//!
//! # Why this file lives in `languages/src/`
//!
//! The language specifications transcribed from the GSLT omnibus paper are
//! PRODUCTION specs (USER ruling, 2026-07-27), so they live beside the other
//! production languages in `languages/src/` and are reachable through the
//! crate's public surface as `mettail_languages::monoid`. Its conformance suite
//! is `languages/tests/monoid.rs` — the same spec/tests split every other
//! production spec uses (`languages/src/calculator.rs` ↔
//! `languages/tests/calculator.rs`).
//!
//! `emit_tests` / `emit_simulator` / `emit_blockly` stay OFF. Those three
//! options are the macro's file-writing switches, so with them off this spec
//! writes no `languages/tests/gen_monoid_*.rs`, no
//! `languages/src/bin/simulate_monoid.rs` and no
//! `languages/src/generated/monoid-*.ts`; what a rung-two presentation has to
//! demonstrate is the *quotient* its equations induce, and that is stated
//! precisely — and only — by the hand-written suite next door.
//!
//! ⚠ Those three `false`s must STAY false, and not because production specs are
//! forbidden generated suites — `ambient`/`calculator`/`lambda`/`rhocalc` all
//! carry theirs. `emit_simulator: true` would make the macro write
//! `languages/src/bin/simulate_monoid.rs` on every compile, and cargo's edition-2021
//! auto-discovery would pick that file up as a binary target with NO
//! `required-features = ["strategies"]` — every hand-declared `[[bin]]` in
//! `languages/Cargo.toml` carries that gate because the generated simulator names
//! `mettail_languages::monoid::strategies::arb_*`, which exists only under the
//! `strategies` feature. A default `cargo build -p languages` would then fail to
//! compile a file nobody wrote. Flipping these on is a change to the macro's
//! emission contract, not a per-language switch.
//!
//! # Clause-by-clause containment (SUPERSET — in fact EQUAL)
//!
//! | omnibus clause | our clause | delta |
//! | --- | --- | --- |
//! | `types { M }` (:434) | `types { M }` | — |
//! | `Unit . M ::= "e" ;` (:437) | identical | — |
//! | `Mul . x:M, y:M \|- x "*" y : M ;` (:438) | identical | — |
//! | `Assoc . \|- (Mul (Mul X Y) Z) = (Mul X (Mul Y Z)) ;` (:442) | identical | — |
//! | `UnitL . \|- (Mul Unit X) = X ;` (:443) | identical | — |
//! | `UnitR . \|- (Mul X Unit) = X ;` (:444) | identical | — |
//! | `rewrites { }` (:447) | identical (empty) | — |
//!
//! 7/7 clauses, character-identical modulo whitespace. No notation deltas.
//!
//! # Notation: the paper is BNFC-flavoured; this file is idiomatic mettail
//!
//! The omnibus's listings carry a labelled-BNF (BNFC) lineage — `Label . Cat ::=
//! "lit" Item … ;` productions and a parameterised `List(X)` carrier. mettail
//! accepts the `::=` form (and this file uses it for nullary constants, exactly as
//! `languages/src/ambient.rs` does), but its idiomatic form is the JUDGEMENT form
//! `Name . ctx |- pattern : Cat ;`, and `List(X)` is spelled `Vec(X)` (the
//! established convention — `rhocalc.rs:57` declares `![Vec<Proc>] as List`).
//! **Superset containment here is SEMANTIC**: every `types` entry, `terms`
//! production, `equations` clause and `rewrites` rule of the paper's version is
//! present with the same meaning; the spelling is ours. Every deviation is
//! tabulated above and explained below.

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr,
    unused_imports,
    dead_code
)]

use mettail_macros::language;

language! {
    name: Monoid,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types { M },

    terms {
        Unit . M ::= "e" ;
        Mul . x:M, y:M |- x "*" y : M ;
    },

    equations {
        Assoc . |- (Mul (Mul X Y) Z) = (Mul X (Mul Y Z)) ;
        UnitL . |- (Mul Unit X) = X ;
        UnitR . |- (Mul X Unit) = X ;
    },

    rewrites { },
}
