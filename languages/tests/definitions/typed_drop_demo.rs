// Task #94 — RED B. See `languages/tests/lowering_disposition_reds.rs` for the assertions.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// ─────────────────────────────────────────────────────────────────────────────
// RED B — the TYPED path: three declinations, and until now not one diagnostic
//         on any lane, not even a runtime `Err`.
//
// The typed path is reached because `Id` is a fold whose OUTPUT category (`Term`) has no native
// type; `needs_typed_dovetail_path` routes such a language to the typed op-enum + native-rule
// dispatcher. That path's three `rule_block` consumers each wrote
// `let (rules_expr, _unsupported) = …`, so a construct the structural lowering refused produced
// no rule, no compile diagnostic, and no runtime error — its refusal was computed and
// immediately discarded three times over.
//
// This grammar carries one declination of each shape the typed path could lose:
//
//   ┌────────────────────┬──────────────────────────────────────────────────────────────┐
//   │ `PairComm`         │ a `Lambda` metapattern: "lambda patterns require binder …"    │
//   │ `FreshSwap`        │ a FRESHNESS premise: `premise_supported` admits only          │
//   │                    │ congruence, so the equation is refused as "has side           │
//   │                    │ conditions" before either orientation is attempted            │
//   │ `Head`             │ a `Vec(Term)` fold parameter: the fold gate's                 │
//   │                    │ `if !all_simple { continue }` — no rule, and (until this       │
//   │                    │ change) no record of any kind, anywhere                        │
//   └────────────────────┴──────────────────────────────────────────────────────────────┘
//
// `Id` is also the positive control on the fold half: a fold on the SAME language, in the SAME
// walk, that IS lowered. Without it, "the fold gate declined `Head`" would be indistinguishable
// from "the fold walk never ran".
language! {
    name: TypedDropDemo,

    options {
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

        // ★ The fold that routes this language to the TYPED path: its output category `Term`
        // has no native type, so it cannot reduce on the `EGraph<String>` path at all.
        // It is also the positive control — a fold that IS delivered.
        Id . a:Term |- "id" "(" a ")" : Term ![{ a.clone() }] fold ;

        // ★ The fold the gate refuses: `xs` is a `Vec(Term)` collection parameter, not a
        // `Simple`/`Base` one. Declared, surfaced in the concrete syntax, and lowered nowhere.
        Head . xs:Vec(Term), d:Term |- "head" "(" "[" xs.*sep(",") "]" "," d ")" : Term ![{
            xs.first().cloned().unwrap_or_else(|| d.clone())
        }] fold ;
    },

    equations {
        // Refused for its `Lambda` metapattern (both orientations).
        PairComm . |- (Pair (Nu ^x.body) other) = (Pair other (Nu ^x.body)) ;
        // Refused for its premise: structural saturation models congruence, not freshness.
        FreshSwap . | x # other |- (Pair (Nu ^x.Zero) other) = (Pair other (Nu ^x.Zero)) ;
    },

    rewrites {},
}
