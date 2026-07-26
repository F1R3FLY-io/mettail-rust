//! `ReservedModel` — the keyword-reservation ENABLED (`auto`) twin of
//! `FortranModel` (PIECE 3).
//!
//! It declares the SAME keyword-vs-variable send structure as `FortranModel`
//! (`SendKw` = literal channel `@ IF ! (q)`, `SendVar` = variable channel
//! `@ n ! (q)`), but sets `options { reserved_keywords: auto }`. Because `IF`
//! is reserved, it no longer lexes as an identifier, so the variable-channel
//! reading is removed and `@IF!(x)` has exactly ONE reading (`SendKw`) — the
//! reservation collapse. `FortranModel` (`none`) yields TWO readings for the
//! byte-identical input. The two languages therefore form the durable
//! dual-mode toggle (`keyword_reservation_tests.rs`).
//!
//! The reserved keyword `IF` sits in a NON-prefix position (immediately after
//! the `@` sigil, exactly like RhoCalc's working `@Nil` / `POutputNil` forms),
//! so it does NOT exercise the WPDA lex-fork prefix-dispatch dependency that
//! blocks reserving RhoCalc's nullary-prefix `PZero` (`|- "Nil" : Proc`). See
//! `rhocalc.rs`'s `options {}` comment for that measured HALT.
//!
//! Like `FortranModel`, this is a real `src` fixture with `emit_tests` /
//! `emit_simulator` / `emit_blockly` disabled.

// Task #11 (extended 2026-07-26): as a library module this definition inherited
// `languages/src/lib.rs`'s crate-level `#![allow(unused_imports, ...)]`. A `#[path]`-included
// module inherits nothing, and each consumer exercises a different slice of the generated
// surface (the parser, the codegen helpers, or neither), so `dead_code` / `unused_imports`
// are expected here rather than a signal. They are allowed at the definition -- the one place
// every consumer shares -- instead of being re-allowed at each `#[path]` site.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: ReservedModel,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `reservedmodel_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_reservedmodel_*.rs`, whose `use mettail_languages::reserved_model::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/reserved_model.rs",
        // ── ENABLE reservation (the `auto` side of the dual-mode matrix) ──
        reserved_keywords: auto,
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
        // Syntax-only reservation demonstration: no reduction semantics, so it
        // is excluded from the production LanguageDefInventory (see the
        // dovetail/ast inventory invariant tests + their parse_only guard).
        parse_only: true,
    },

    types {
        Stmt
        Term
        ![i64] as Int
    },

    terms {
        IntTerm . i:Int |- i : Term ;

        // Literal keyword channel (`@ IF ! (q)`). Declared first (more specific).
        SendKw . q:Term |- "@" "IF" "!" "(" q ")" : Stmt ;
        // Variable channel (`@ n ! (q)`). Under `auto`, `IF` is reserved and
        // cannot fill `n`, so `@IF!(x)` yields ONLY `SendKw` — one reading.
        SendVar . n:Term, q:Term |- "@" n "!" "(" q ")" : Stmt ;
    },

    equations {},

    rewrites {},
}
