// Task #101 — FIXTURE 1. See `languages/tests/collection_fold_carriers.rs` for the assertions.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// ─────────────────────────────────────────────────────────────────────────────
// SeqCarrierDemo — the ORDERED whole-constructor collection, which the corpus
//                  does not contain a single instance of.
//
// Every `VariantKind::Collection` in the production tree is a `HashBag`
// (`PPar` / `PParInternal`). So the two claims Task #101 makes about the ORDERED
// whole-constructor arm — that it lowers to `ENode::new(Cat_Label, [seq_leaf])`
// rather than a bare leaf, and that a fold over it fires — are claims about an
// EMPTY SET unless a live grammar exercises them. This is that grammar.
//
//   ┌───────────┬────────────────────────────────────────────────────────────────┐
//   │ `Boxed`   │ a single-`Vec` constructor.                                    │
//   │ `Crated`  │ a SECOND single-`Vec` constructor of the SAME category, with    │
//   │           │ the same element type — so the two differ ONLY by constructor  │
//   │           │ identity. Before #101 both lowered to a BARE                   │
//   │           │ `FieldOpaque(format!("{:?}", values))` leaf with no constructor │
//   │           │ node, so `box(0)` and `crate(0)` produced byte-identical e-node │
//   │           │ content and HASH-CONSED INTO ONE E-CLASS: a rewrite keyed on    │
//   │           │ one matched the other. That is the identity defect §4 repairs.  │
//   │ `Firstly` │ a single-`Vec` FOLD (`VariantKind::Collection` + `OrderedSeq`), │
//   │           │ whose LHS is the ordinary positional `Pattern::app(op, [var])`  │
//   │           │ because the constructor node has exactly one child — the        │
//   │           │ sequence leaf.                                                  │
//   │ `Pair`    │ a two-child container, present only so one term can hold both   │
//   │           │ `Boxed` and `Crated` and the report can be asked whether their  │
//   │           │ e-classes differ.                                               │
//   └───────────┴────────────────────────────────────────────────────────────────┘
//
// `Firstly`'s OUTPUT category `Term` has no native type, which is what routes
// this language to the TYPED Dovetail path (`needs_typed_dovetail_path`) where
// the op enum, the sequence carrier and the fold dispatcher live.
language! {
    name: SeqCarrierDemo,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
        hosted_in: "tests/definitions/seq_carrier_demo.rs",
    },

    types {
        Term
    },

    terms {
        Zero . |- "0" : Term ;

        Pair . a:Term, b:Term |- "pair" "(" a "," b ")" : Term ;

        // ★ Two DISTINCT single-`Vec` constructors of ONE category. Their payloads are the
        // same type, so equal payloads used to collide.
        Boxed . xs:Vec(Term) |- "box" "(" xs.*sep(",") ")" : Term ;
        Crated . xs:Vec(Term) |- "crate" "(" xs.*sep(",") ")" : Term ;

        // ★ The single-`Vec` fold. `xs` binds through the sequence leaf that is child 0 of the
        // `Firstly` constructor node, and the body reads it as an owned `Vec<Term>`.
        Firstly . xs:Vec(Term) |- "first" "(" xs.*sep(",") ")" : Term ![{
            xs.first().cloned().unwrap_or(Term::Zero)
        }] fold ;
    },

    equations {},

    rewrites {},
}
