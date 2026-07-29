// Task #101 — FIXTURE 2. See `languages/tests/collection_fold_carriers.rs` and
// `languages/tests/lowering_disposition_inventory.rs` for the assertions.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// ─────────────────────────────────────────────────────────────────────────────
// MapParamRefusalDemo — ★ THE GATE DID NOT OPEN TOO FAR, on a NON-EMPTY set.
//
// Task #101 admits collection fold parameters PER CARRIER, not as a class:
//
//   ┌──────────────────────────┬───────────┬──────────────────────────────────────┐
//   │ `Vec(T)`                 │ ORDERED   │ ADMITTED — `Debug` is deterministic  │
//   │                          │           │ and `Eq`-agreeing for an ordered     │
//   │                          │           │ vector, so a labelled leaf carrying  │
//   │                          │           │ the whole value has a total inverse. │
//   │ `HashBag(T)` (whole ctor)│ AC        │ ADMITTED — an n-ary bag node that    │
//   │                          │           │ already had both a lowering and an   │
//   │                          │           │ inverse.                             │
//   │ `HashSet(T)`             │ OPAQUE    │ REFUSED — `Debug` does NOT agree     │
//   │ `HashMap(K,V)`           │ (map/set) │ with `Eq`; the e-graph content key   │
//   │ `PathMap(K,V)`           │           │ for these is their SORTED `Display`, │
//   │                          │           │ so there is NO stored order to       │
//   │                          │           │ invert to and a labelled carrier     │
//   │                          │           │ would claim an inverse that does     │
//   │                          │           │ not exist.                           │
//   └──────────────────────────┴───────────┴──────────────────────────────────────┘
//
// The corpus contains ZERO folds with a set/map parameter, so "the gate did not open too far"
// is an assertion about an empty set unless a live grammar declares one. `MapFold` is that
// instance: `m:HashMap(Proc, Proc)` is a fold parameter of a keyed container, it is refused,
// and the refusal NAMES the type.
//
// ⚠ MEASURED, AND RECORDED SO IT IS NOT RE-ATTEMPTED: a `HashSet(Proc)` fold parameter — the
// one shape that reaches the gate's `CollectionCarrier::Opaque` arm through
// `TypeExpr::Collection` rather than `TypeExpr::Map` — CANNOT BE DECLARED AT ALL today, for a
// reason entirely outside the fold gate. A `HashSet` collection FIELD emits a raw
// `std::collections::HashSet<Proc>` AST field, and that type implements neither `Hash` (needed
// by `iterative_hash` / `semantic_hash`), nor `Ord` (needed by `iterative_cmp`), nor
// `BoundTerm` (needed by the `mettail_runtime::BoundTerm` derive) — four hard compile errors
// before any lowering runs. The corpus's set-shaped data uses the `HashSetLit` runtime wrapper,
// which is available only to a collection-LITERAL CATEGORY (`![HashSetLit<Proc>] as Set`), not
// to a constructor field. So the `Opaque` arm is a FAIL-CLOSED default over the containers
// `CollectionType` can name, and `HashMap` is its only expressible instance; the gate refuses
// both, by carrier and by residual respectively.
//
// `VecFold` is the ★ POSITIVE CONTROL: a fold on the SAME language, found by the SAME walk,
// whose collection parameter IS lowered. Without it, "the gate declined `MapFold`" would be
// indistinguishable from "the fold walk never ran".
language! {
    name: MapParamRefusalDemo,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
        hosted_in: "tests/definitions/map_param_refusal_demo.rs",
    },

    types {
        Proc
    },

    terms {
        PZero . |- "0" : Proc ;

        // ★ POSITIVE CONTROL — an ORDERED collection parameter, Delivered.
        VecFold . xs:Vec(Proc), d:Proc
            |- "vfold" "(" "[" xs.*sep(",") "]" "," d ")" : Proc ![{
                xs.first().cloned().unwrap_or_else(|| d.clone())
            }] fold ;

        // ★ REFUSED — `HashMap(Proc, Proc)` is a `TypeExpr::Map`, refused by the residual arm.
        MapFold . m:HashMap(Proc, Proc), d:Proc
            |- "mfold" "(" "<" m.*sep(",") ">" "," d ")" : Proc ![{
                d.clone()
            }] fold ;
    },

    equations {},

    rewrites {},
}
