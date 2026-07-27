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

// Stage 3b demonstration language: the canonical single-receive Rholang COMMUNICATION rule
//
//     Comm . |- (PPar {(PFor N cont), (POutput N Q), ...rest}) ~> (PPar {(eval cont Q), ...rest})
//
// i.e. `for(y <- N){ cont } | N!(Q)  ~>  cont[Q/y]`, spliced back into the residual bag. It is the
// FIRST NON-LINEAR AC firing: the channel metavariable `N` occurs in BOTH the receive `(PFor N …)`
// and the send `(POutput N …)`, so the AC selection is valid only when the two occurrences are
// name-equal (`N ≡ N`). This composes, in ONE atomic COMM on the live f1r3node reducer:
//
//   * HashBag AC over `PPar` with k=2 structured fixed elements (the `PFor` receive and the
//     `POutput` send) + `...rest` — the order-independent process-soup match (`ac_bag_pattern`
//     analogue), reusing the `AcBagDemo` bag-RHS carrier (`reflect_hashbag_soup_par`);
//   * a NON-LINEAR consistency guard (`Receive.condition`, the `where`-clause `EEq` over the two
//     structured elements' channel σ slots) enforcing `N ≡ N`, reject-safe (a mismatched-channel
//     soup leaves the data resting — `merge_substs → None`);
//   * host-computed capture-avoiding substitution `cont[Q/y]` (the `(eval cont Q)` operator IS the
//     substitution — see `LambdaDemo`) delivered as the firing's CONTRACTUM at a dedicated σ slot,
//     exactly like the Stage 3c binder / Stage 3e native paths.
//
// `PFor . n:Name, ^x.p:[Name -> Proc]` receives on the channel `n` and binds `^x.p` (a
// `[Name -> Proc]` binder); `POutput . n:Name, q:Name` sends the name `q` on the channel `n`. Names
// are quoted nullary processes `@0`/`@1`/`@2`/`@3` (`NQuote`), so distinct channels are available
// for the positive (matching) and negative (mismatched) firing checks without single-letter Name
// keywords colliding with binder-variable identifiers.
//
// The concrete redex `{ for(y <- @0){ y!(@2) } | @0!(@1) }` reduces (both channels are `@0`) to
// `{ @1!(@2) }` — the body `y!(@2)` with the sent `@1` substituted for the bound `y` — and
// `{ for(y <- @0){ y!(@2) } | @0!(@1) } ≠ { @1!(@2) }`, so a positive OUT observation of `{ @1!(@2) }`
// is non-vacuous evidence Rholang's communication rule fired as ONE COMM with the σ + substitution
// Dovetail computed. The mismatched soup `{ for(y <- @0){ y!(@2) } | @1!(@3) }` (channels `@0` ≠
// `@1`) does NOT fire — the non-linear `Receive.condition` vetoes it.
//
// Kept SEPARATE from the full `Rholang` (whose communication rides the entangled multi-`&`
// `PForUser` query engine, `receive::try_comm_rw_proc`) so the canonical single-receive Comm is
// isolated exactly as `SwapDemo`/`AcDemo`/`AcBagDemo`/`CtxDemo`/`LambdaDemo`/`NativeDemo` isolate
// their respective firing families.
language! {
    name: CommDemo,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `commdemo_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_commdemo_*.rs`, whose `use mettail_languages::commdemo::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/commdemo.rs",
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        Name
    },

    terms {
        PZero . |- "0" : Proc ;

        // Distinct nullary channel names `na`/`nb`/`nc`/`nd`. Kept nullary (not a quoted-process
        // `@ p`) so their grammar is a single leaf literal: a prefix `"@" p` matches the
        // scalar-operator shape `[Literal, Param]` and would be mis-lowered as a native system
        // process, and the demo needs only distinct names for the matching / mismatched channel
        // checks — the substitution semantics (a bound Name replaced by a sent Name) are unchanged.
        Na . |- "na" : Name ;
        Nb . |- "nb" : Name ;
        Nc . |- "nc" : Name ;
        Nd . |- "nd" : Name ;

        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;

        POutput . n:Name, q:Name |- n "!" "(" q ")" : Proc ;

        PFor . n:Name, ^x.p:[Name -> Proc]
            |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
    },

    equations {},

    rewrites {
        Comm . |- (PPar {(PFor N cont), (POutput N Q), ...rest})
            ~> (PPar {(eval cont Q), ...rest}) ;
    },
}
