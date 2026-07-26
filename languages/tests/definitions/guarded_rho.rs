//! GuardedRho — minimal rho-calculus-like language with a guarded
//! receive constructor that demonstrates source-level predicated typing.
//!
//! This is the smoke-test language for the predicated-types feature.
//! Phase 14 of the implementation plan in
//! `/Users/dylon/.claude/plans/compressed-sauteeing-valiant.md`.
//!
//! ## Constructors
//!
//! - `PZero` — `0` — nil process
//! - `PPar` — `P | Q` — parallel composition
//! - `POutput` — `n!(p)` — send `p` on channel `n`
//! - `PGuardedInput` — `for(x <- n) where guard { p }` — guarded receive
//! - `NQuote` — `@(p)` — quote `p` as a name
//! - `PDrop` — `*n` — dereference name
//!
//! ## The `?guard:Guard` slot
//!
//! `PGuardedInput` declares a `?guard:Guard` parameter — a runtime
//! `mettail_runtime::BehavioralPred` field on the generated enum
//! variant. Each user-source `for ... where ...` term carries its own
//! per-instance predicate.
//!
//! At source-parse time, the macro-generated parser hits the
//! `GuardExpression` syntax item and invokes the predicate sublanguage
//! parser (Phase 1B + Phase 2G), which produces a runtime
//! `BehavioralPred::RelationQuery` value referencing one of the
//! declared logic relations.
//!
//! ## Logic relations
//!
//! - `halts(Proc)` — external relation populated by user code
//! - `safe(Proc)` — external relation populated by user code
//!
//! ## Equations
//!
//! Parallel composition is commutative + associative + has unit `PZero`.

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
    name: GuardedRho,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `guardedrho_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_guardedrho_*.rs`, whose `use mettail_languages::guarded_rho::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/guarded_rho.rs",
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        Name
        ![i64] as Int
    },

    guards {
        channels {
            channel Name;
            join PGuardedInput(ch: Name);
        }
    },

    terms {
        PNil . |- "Nil" : Proc ;

        CastInt . k:Int |- k : Proc ;

        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;

        POutput . n:Name, p:Proc
            |- n "!" "(" p ")" : Proc ;

        PGuardedInput . n:Name, ?guard:Guard, ^x.p:[Name -> Proc]
            |- "for" "(" x "<-" n "where" guard ")" "{" p "}" : Proc ;

        NQuote . p:Proc
            |- "@" p : Name ;

        PDrop . n:Name
            |- "*" n : Proc ;
    },

    equations {
        // Commutativity and associativity are inherent in HashBag.
    },

    logic {
        relation halts(Proc);
        relation safe(Proc);
    },
}
