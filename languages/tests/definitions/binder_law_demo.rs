// Task #94 — RED A. See `languages/tests/lowering_disposition_reds.rs` for the assertions.
//
// A `#[path]`-included module inherits none of `languages/src/lib.rs`'s crate-level allows, and
// each consumer exercises a different slice of the generated surface, so `dead_code` /
// `unused_imports` are expected here rather than a signal.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// ─────────────────────────────────────────────────────────────────────────────
// RED A — the STRING path with a binder handler: a declined equation whose
//         diagnostic reaches NOTHING.
//
// This grammar is built to sit at declination class D4: a construct whose refusal IS recorded
// by the lowering and then DISCARDED by the consumer, so that no artifact anywhere — generated
// source, runtime error, test — mentions it.
//
// The three conditions that put it there:
//
//   1. `Nu` is a surface SINGLE-binder constructor over the primary category `Term`, and the
//      language declares equations, and it has no `RhoNativeJoin` guard obligation. Those are
//      exactly the three conditions of `should_emit_binder_congruence`, so the generated report
//      floats binders outward instead of failing closed — and the `native_gate` that would have
//      embedded the declination diagnostic into the generated source is emitted as `quote!{}`.
//      The diagnostic is computed and then dropped on the floor.
//
//   2. Nothing routes this language to the typed path: no folds, no rewrites. So it takes the
//      `EGraph<String>` path, the only path that ever embedded a declination diagnostic at all.
//
//   3. `PairComm`'s two sides each carry a `Lambda` metapattern, which
//      `pattern_to_dovetail` refuses with "lambda patterns require binder lowering". Both
//      orientations are refused, so the law is lowered NOWHERE.
//
// ★ WHY THIS SHAPE AND NOT A FLOAT LAW. A binder-shaped equation is not automatically a
// declination: `ScopeExtrusion`-style float laws (`C(…, ν x. P, …) = ν x. C(…, P, …)`) are
// discharged in full by the generated binder-congruence normal form, and the inventory must say
// so rather than cry wolf. `PairComm` is deliberately NOT of that shape — the binder is at the
// root of neither side, so `classify_equation_float_disposition` cannot recognize it — which is
// what makes it a genuine declination rather than a mis-attribution.
//
// The law itself is ordinary commutativity of `Pair`, stated over a `Nu`-headed component. It
// is a law a user would reasonably write and would reasonably expect to hold.
language! {
    name: BinderLawDemo,

    options {
        // A demonstration grammar, not a production language: no generated suite, no
        // simulation CLI, no Blockly blocks. The assertions live in the hand-written host.
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Term
        // ⚠ A SECOND category, present only to keep the generated
        // `binder_congruence.rs` compilable. That module emits
        // `<Lang>TermInner::…` match arms unconditionally, but the term-wrapper
        // generator emits a `<Lang>TermInner` enum only for a MULTI-type language, so a
        // SINGLE-type language satisfying `should_emit_binder_congruence` (a surface
        // single binder over the primary category + non-empty equations + no
        // `RhoNativeJoin` obligation) generates code that does not compile. No bundled
        // language hits it — Ambient and Pi are both multi-type — so it has never been
        // observed. Logged as an out-of-scope defect by Task #94, whose brief fences
        // `binder_congruence.rs` off from this change (`359220f3` fixed an unsound Pi float
        // there and its guards are live). `Tag` is otherwise inert: nothing references it.
        Tag
    },

    terms {
        Nu . ^x.body:[Term -> Term] |- "nu " x "." body : Term ;
        Pair . a:Term, b:Term |- "pair" "(" a "," b ")" : Term ;
        Zero . |- "0" : Term ;
        Tg . |- "tag" : Tag ;
    },

    equations {
        // Commutativity of `Pair`, over a binder-headed component. `Nu` heads NEITHER side of
        // the equation, so this is not a float-across-constructor law and not a binder-binder
        // commutation law — it is exactly the case that lowers nowhere.
        PairComm . |- (Pair (Nu ^x.body) other) = (Pair other (Nu ^x.body)) ;
    },

    rewrites {},
}
