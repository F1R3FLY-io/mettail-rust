// Sole-collection lane FIXTURE. See `languages/tests/collection_fold_carriers.rs` for the
// assertions.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// ─────────────────────────────────────────────────────────────────────────────
// SoleCollectionCarrierDemo — every carrier and element shape of the sole-collection lane.
//
// A rule whose only field is a collection takes the sole-collection lane
// (`VariantKind::Collection`). Each emitter of that lane must follow the DECLARED carrier
// and the DECLARED element:
//
//   ┌──────────────┬─────────────────────────┬────────────────────────────────────────────┐
//   │ Constructor  │ Field                   │ What the lane must emit                    │
//   ├──────────────┼─────────────────────────┼────────────────────────────────────────────┤
//   │ PPar         │ HashBag(Proc) : Proc    │ the auto-flatten helper `insert_into_ppar` │
//   │ PNames       │ HashBag(Name) : Proc    │ direct `HashBag::insert`, no helper        │
//   │ PSet         │ HashSet(Proc) : Proc    │ `mettail_runtime::HashSetLit<Proc>`        │
//   │ PNameSet     │ HashSet(Name) : Proc    │ `mettail_runtime::HashSetLit<Name>`        │
//   │ PSeq         │ Vec(Proc) : Proc        │ `Vec<Proc>`                                │
//   │ PNameSeq     │ Vec(Name) : Proc        │ `Vec<Name>`                                │
//   │ PNameBag     │ HashBag(Name), BNF form │ direct insert, BNF field emitter           │
//   │ PSetBnf      │ HashSet(Proc), BNF form │ `HashSetLit<Proc>`, BNF field emitter      │
//   │ PSeqBnf      │ Vec(Proc), BNF form     │ `Vec<Proc>`, BNF field emitter             │
//   └──────────────┴─────────────────────────┴────────────────────────────────────────────┘
//
// The auto-flatten helper type-checks only when the element is the owner category
// (BinderFloatCanonicalization.v Part 5, `helper_applies_only_when_well_typed`). Before
// 2026-10-20 the carrier alone decided, so `PNames` and `PNameBag` did not compile
// (`old_gate_emits_and_calls_an_ill_typed_helper`), and a `HashSet` field got a raw
// `std::collections::HashSet`, which has no `BoundTerm`, `Hash` or `Ord`.
//
// Data-category collections preserve their structural payload during generic semantic
// operations. The fixture includes embedded object terms to test that boundary.
//
// The three BNF rules have the same shapes as the `Vec(Value) : Value` and
// `HashBag(Field) : Value` spellings that `languages/src/json.rs` records as failed.
//
// `NameBagFold` is a fold over a cross-category bag, so the typed inverse of the AC bag
// lowering is emitted for a cross-category element. `SetFold` is a fold over a `HashSet`
// parameter: the fold gate refuses an opaque carrier and names the refused type.
language! {
    name: SoleCollectionCarrierDemo,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
        hosted_in: "tests/definitions/sole_collection_carrier_demo.rs",
    },

    types {
        Proc
        Name
        data Meta
    },

    terms {
        PZero . |- "0" : Proc ;
        NLit . |- "n" : Name ;
        MLit . |- "m" : Meta ;
        MOther . |- "other" : Meta ;
        MProc . value:Proc |- "meta" "(" value ")" : Meta ;

        PPar . ps:HashBag(Proc) |- "par" "{" ps.*sep("|") "}" : Proc ;
        PNames . ns:HashBag(Name) |- "names" "{" ns.*sep(",") "}" : Proc ;
        PMetas . ms:HashBag(Meta) |- "metas" "{" ms.*sep(",") "}" : Proc ;
        PMetaSet . ms:HashSet(Meta) |- "metaset" "{" ms.*sep(",") "}" : Proc ;
        PMetaSeq . ms:Vec(Meta) |- "metaseq" "[" ms.*sep(",") "]" : Proc ;
        PMetaBagBnf . Proc ::= HashBag(Meta) sep "," delim "mbag" "end" ;
        PMetaSetBnf . Proc ::= HashSet(Meta) sep "," delim "mset" "end" ;
        PMetaSeqBnf . Proc ::= Vec(Meta) sep "," delim "mseq" "end" ;
        PSet . s:HashSet(Proc) |- "set" "{" s.*sep(",") "}" : Proc ;
        PNameSet . s:HashSet(Name) |- "nameset" "{" s.*sep(",") "}" : Proc ;
        PSeq . xs:Vec(Proc) |- "seq" "[" xs.*sep(",") "]" : Proc ;
        PNameSeq . xs:Vec(Name) |- "nameseq" "[" xs.*sep(",") "]" : Proc ;
        PNameBag . Proc ::= HashBag(Name) sep "," delim "bnames" "end" ;
        PSetBnf . Proc ::= HashSet(Proc) sep "," delim "bset" "end" ;
        PSeqBnf . Proc ::= Vec(Proc) sep "," delim "bseq" "end" ;

        NameBagFold . ns:HashBag(Name) |- "nfold" "(" ns.*sep(",") ")" : Proc ![{
            Proc::PZero
        }] fold ;
        SetFold . s:HashSet(Proc) |- "sfold" "(" s.*sep(",") ")" : Proc ![{
            Proc::PZero
        }] fold ;
    },

    equations {},

    rewrites {},
}
