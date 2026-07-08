#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Stage AC2b demonstration language: the linear with-rest HashBag AC base rewrite whose RHS is
// itself a NESTED BAG — `PPar{x, ...rest} ~> PPar{Mark(x), ...rest}` — a bag-TRANSFORMING rule
// (one fixed element is transformed to `Mark(x)`, the residual `rest` carried). This is the
// bag-VALUED RHS analogue of `AcDemo` (whose RHS `Wrap(x)` is a plain term): it exercises the
// codegen `reflect_hashbag_soup_par` path (the AC receiver body's `⟦R⟧σ` is the process-soup
// carrier) and the runtime `decode_ac_bag_soup` path (OUT is the transformed bag, a bare soup)
// end-to-end.
//
// `Mark` is IDEMPOTENT (`Mark(Mark(x)) = Mark(x)`), which makes equality saturation TERMINATE: the
// rewrite would otherwise loop forever building `Mark(Mark(… x))` (the RHS keeps the bag, so it is
// always re-matchable — unlike `AcDemo`'s non-bag `Wrap(x)` RHS). With idempotence the reachable
// terms collapse to the fixed point `PPar{Mark(A), Mark(B), Mark(C)}` (each element marked at most
// once), so the Dovetail report converges (Complete) and surfaces the firing σ the AC injection
// reads. The idempotence equation is a HOST (Dovetail) saturation concern only — the installed Rho
// receiver marks each picked element exactly once, so OUT is `PPar{Mark(e), <the rest>}`.
//
// It is kept SEPARATE from `AcDemo` (rather than adding a second rewrite) so the two languages'
// firing suites do not interfere: the same subject `PPar{A|B|C}` would fire BOTH rules if they
// shared a language, changing each other's firing counts. `AcBagDemo` is the direct prerequisite
// shape for RhoCalc's `Comm` rule, whose RHS `PPar{P[Q/y], ...rest}` is likewise a bag.
//
// `PPar{A | B | C}` reduces to `PPar{Mark(A), B, C}` / `PPar{Mark(B), A, C}` / `PPar{Mark(C), A, B}`
// (one bag element marked, picked by the native AC matcher; the rest spliced back via
// `add_flattened_bag`), so a positive OUT observation of the transformed bag is non-vacuous
// evidence a bag-RHS AC rewrite fired as a COMM with the σ Dovetail computed.
language! {
    name: AcBagDemo,

    options {
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
        Mark . x:Proc |- "mark" "(" x ")" : Proc ;
        PPar . ps:HashBag(Proc) |- "#{" ps.*sep("|") "}#" : Proc ;
    },

    equations {
        // Idempotent marking: `Mark(Mark(x)) = Mark(x)`. This bounds the bag-transforming rewrite
        // to the fixed point where every element is marked at most once, so equality saturation
        // terminates (Complete) rather than looping on `Mark(Mark(… x))`.
        MarkIdem . |- (Mark (Mark x)) = (Mark x) ;
    },

    rewrites {
        AcBagStep . |- (PPar {x, ...rest}) ~> (PPar {(Mark x), ...rest}) ;
    },
}
