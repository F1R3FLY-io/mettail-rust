#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Stage 4 S-binder SLICE 3b demonstration language: the Ambient-calculus `OpenRule` fired IN RHO
// via the SPREAD, UNDER a `new(x, ·)` binder.
//
//     OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest}) ~> (PPar {P, Q, ...rest})
//
// `AmbNewDemo` is the `AmbDemo` OpenRule fragment PLUS the `PNew` binder
//
//     PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc
//
// so a redex `new(x, { open(x, A) | x[B] })` — the ambient name IS the bound `new`-scoped name `x`
// — exercises the structural-AC spread matcher UNDER a binder. The reflection is ALREADY generic
// (macro `reflect_category_fn`): `PNew` (empty pre-scope fields) reflects to the reserved single-
// child `^lambda([⟦body⟧])`, and each bound occurrence of `x` reflects to `^bound(peano(depth))`.
// The structural-AC match walk (`structural_ac_match_install_at`) descends the `^lambda` child into
// the operand bag with NO binder-specific code (slice 3a's `ac_match_call_descends_through_lambda_
// to_the_bag`), locates it, and co-installs a per-site MATCH receiver that binds the two structured
// elements + `P`/`Q` + `rest` FROM the bag and splices `{P, Q}` on `@out` under the non-linear
// `N ≡ N` guard. Both occurrences of `x` reflect to the SAME `^bound(peano(0))` (bound by the ONE
// enclosing `new`), so the guard holds; a DISTINCT-binder redex `new(x, new(y, {open(x,A) | y[B]}))`
// reflects `x`/`y` to DIFFERENT `^bound` depths, so the guard VETOES (reject-safe).
//
// The observed reduct is the HOLE bag `{ A | B }` — the OpenRule firing on the inner par. Re-wrapping
// it as `new(x, { A | B })` (the `NewCong` congruence lift) is the deferred slice 3c; this demo
// observes the hole reduct, exactly as the base nested-redex tests observe the inner contractum
// without whole-term reassembly.
//
// Kept SEPARATE from `AmbDemo` (no binder) and the full `Ambient` (whose `InRule`/`OutRule` are DEEP
// nested-ambient AC reductions and whose structural-congruence equations carry the untyped binder-
// evaluator float) so the CLEAN "structural-AC under a `new`" firing is isolated — exactly as the
// sibling demos isolate their firing families. Process leaves `A`/`B` are CAPITALIZED (like the
// `AmbDemo`/`SwapDemo` leaves) so they do not collide with the auto-generated lowercase process/name
// VARIABLE identifiers, and `na`/`nb` are distinct nullary ambient-name leaves for the no-binder
// sibling checks.
language! {
    name: AmbNewDemo,

    options {
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        Name
    },

    terms {
        PZero . |- "0" : Proc ;

        // Distinct nullary processes `A`/`B` — the payloads `open(n, ·)` dissolves and `n[·]` carries.
        PA . |- "A" : Proc ;
        PB . |- "B" : Proc ;

        // Distinct nullary ambient names `na`/`nb` for the no-binder sibling checks.
        Na . |- "na" : Name ;
        Nb . |- "nb" : Name ;

        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;

        // The ambient-dissolution capability `open(n, p)` and the ambient `n[p]`.
        POpen . n:Name, p:Proc |- "open" "(" n "," p ")" : Proc ;

        PAmb . n:Name, p:Proc |- n "[" p "]" : Proc ;

        // The `new(x, p)` name binder — `x` binds a `Name` scoped over the process body `p`. Reflects
        // to the reserved single-child `^lambda([⟦p⟧])`; bound occurrences of `x` ride `^bound(peano)`.
        PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc ;
    },

    equations {},

    rewrites {
        OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
            ~> (PPar {P, Q, ...rest}) ;
    },
}
