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

// Stage AC-U3 demonstration language: the linear with-rest HashBag AC base rewrite
// `PPar{x, ...rest} ~> Wrap(x)` over nullary `A`/`B`/`C`. This is the ONLY bundled
// language shape that exercises the in-Rho AC firing path (AC-U0..U3) end-to-end:
// SwapDemo has no AC rule, and Rholang's `PPar` rules are contextual (`ParCong`) or
// equations (`Extrude`) rather than a base rewrite over a with-rest HashBag.
//
// Promoted to a generated `language!` (exactly like `swapdemo`) so the full
// dovetail-driven Rho AC σ-injection path can be exercised end-to-end in
// `rholang-runtime/tests/rho_net_ac_firing.rs`: the generated `dovetail_report_for`
// resolves + bare-ifies the AC firing's σ (element `x` + residual `rest` = the
// canonical bag over the complement), and the generated
// `rho_net_invocation_from_dovetail_to` reconstructs the WHOLE bag from that σ and
// builds the AC injection the runtime runs against the installed AC receiver.
//
// `PPar{A | B | C}` reduces to `Wrap(A)` / `Wrap(B)` / `Wrap(C)` (one bag element,
// picked by the native AC matcher), so a positive OUT observation is non-vacuous
// evidence the AC rewrite fired as a COMM with the σ Dovetail computed.
language! {
    name: AcDemo,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `acdemo_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_acdemo_*.rs`, whose `use mettail_languages::acdemo::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/acdemo.rs",
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        ![mettail_runtime::HashBag<Proc>] as Bag {
            open_parts: ["#{"],
            close_parts: ["}#"],
            sep: "|",
        }
    },

    terms {
        A . |- "A" : Proc ;
        B . |- "B" : Proc ;
        C . |- "C" : Proc ;
        Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
        PPar . ps:HashBag(Proc) |- "#{" ps.*sep("|") "}#" : Proc ;
    },

    equations {},

    rewrites {
        AcStep . |- (PPar {x, ...rest}) ~> (Wrap x) ;
    },
}
