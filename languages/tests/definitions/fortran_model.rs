//! `FortranModel` — a keyword-reservation OPT-OUT fixture (PIECE 3).
//!
//! This mini-language models Fortran's defining lexical property: **it has no
//! reserved words**. In (fixed-form) Fortran, `DO`, `IF`, `THEN` are ordinary
//! identifiers that may name variables; the classic illustration is
//!
//! ```text
//!     DO 10 I = 1 , 5      ! a DO-loop: iterate I from 1 to 5
//!     DO 10 I = 1.5        ! an assignment: DO10I := 1.5  (DO10I is a variable)
//! ```
//!
//! where a single comma vs. decimal point flips the meaning. Both MUST parse —
//! the tokenizer cannot commit `DO` to a keyword. This language opts out of
//! keyword reservation via `options { reserved_keywords: none }`, so a
//! keyword-shaped literal terminal (`DO`) keeps its generic `Ident` co-accept
//! and therefore ALSO lexes as an identifier. Combined with the implicit
//! per-category variable variant (`Term::…Var`), a keyword-shaped token in
//! identifier position yields BOTH readings — full ambiguity is retained.
//!
//! Contrast with RhoCalc (`options { reserved_keywords: auto }`), where `Nil`
//! is reserved and `@Nil` has exactly one reading. The SAME grammar-derived
//! mechanism drives both; only the per-language `reserved_keywords` toggle
//! differs. See `languages/tests/gen_fortran_model_prop.rs` (this language,
//! opt-out) and `languages/tests/keyword_reservation_tests.rs` (RhoCalc,
//! reserve) for the durable dual-mode test matrix.
//!
//! It is a real `src` fixture (not a test-local `language!`) for the same
//! reason as `appsubst`: the macro emits crate-coupled artifacts per
//! invocation. `emit_tests` / `emit_simulator` / `emit_blockly` are disabled
//! so the macro does not clobber the hand-written durable test file and does
//! not autodiscover a strategies-only simulation binary.

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
    name: FortranModel,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `fortranmodel_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_fortranmodel_*.rs`, whose `use mettail_languages::fortran_model::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/fortran_model.rs",
        // ── OPT-OUT: no reserved words (full ambiguity retained) ──
        // `DO`/`IF`/`THEN` remain usable as identifiers; a keyword-shaped
        // token in identifier position keeps BOTH the keyword reading and the
        // variable reading. This is the Fortran-style escape hatch. `none` is
        // also the global default, so this language is byte-identical to
        // omitting the option — it is written explicitly for documentation.
        reserved_keywords: none,
        // Do not auto-generate tests (protects the hand-written durable test
        // file `tests/gen_fortran_model_prop.rs`), simulation binary, or
        // Blockly blocks for this parsing-only fixture.
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
        // Syntax-only reservation demonstration: no reduction semantics, so it
        // is excluded from the production LanguageDefInventory (the dovetail/ast
        // inventory invariant tests; the guard there requires a parse_only
        // language to carry no equations/rewrites/logic).
        parse_only: true,
    },

    types {
        Stmt
        Term
        ![i64] as Int
        ![f64] as Real
    },

    terms {
        // ── Literal injections into Term ──
        IntTerm  . i:Int  |- i : Term ;
        RealTerm . r:Real |- r : Term ;

        // ── Keyword-vs-variable fork ──
        // Mirrors RhoCalc's `POutputNil` (literal `@ Nil ! (q)`) vs
        // `POutputQuoted` (`@ n:Name ! (q)`, channel is a variable). The
        // channel position is a nested `Term`, so a keyword-shaped token there
        // competes between the LITERAL keyword rule and the VARIABLE rule.
        //
        // `SendKw` — literal keyword channel `IF` (declared first, more specific).
        SendKw . q:Term |- "@" "IF" "!" "(" q ")" : Stmt ;
        // `SendVar` — general channel `n:Term`. With reservation OFF, `IF` in
        // the `n` position lexes as an identifier → `TVar("IF")`, so `@IF!(x)`
        // forks into BOTH `SendKw` (literal) and `SendVar(TVar("IF"), …)`
        // (variable). Under `reserved_keywords: auto` the variable reading is
        // removed and only `SendKw` remains — the reservation toggle.
        SendVar . n:Term, q:Term |- "@" n "!" "(" q ")" : Stmt ;

        // ── Fortran DO archetype (the `DO 10 I = …` ambiguity) ──
        // This WPDA dispatches a *prefix keyword* on the following PUNCTUATION
        // token (like RhoCalc's `for( … )` / `new( … )`), so the fixed-form
        // `DO 10 I = …` (keyword immediately followed by a number) is written
        // here in its parenthesized analog `DO(10, I) = …`. The DECISIVE part
        // of the archetype is preserved verbatim: a top-level comma vs. a
        // decimal point flips loop ↔ assignment.
        //
        // Loop form: a top-level comma yields two integer bounds.
        //   `DO(10, I) = 1 , 5`
        DoLoop . lbl:Int, v:Term, lo:Int, hi:Int
            |- "DO" "(" lbl "," v ")" "=" lo "," hi : Stmt ;
        // Assignment form: a real (decimal) right-hand side.
        //   `DO(10, I) = 1.5`
        DoAssign . lbl:Int, v:Term, val:Real
            |- "DO" "(" lbl "," v ")" "=" val : Stmt ;

        // Plain assignment: `<var> = <real>`. A keyword-shaped variable (`IF`)
        // in LHS position assigns to a variable named `IF` when unreserved.
        Assign . v:Term, val:Real |- v "=" val : Stmt ;
    },

    equations {},

    rewrites {},
}
