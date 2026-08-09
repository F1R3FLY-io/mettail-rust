//! Named regression witnesses for the historical Rholang proptest corpus.
//!
//! The corpus contains 54 minimized constructor trees. Fifty-three have an
//! exact representation in the current grammar and are reconstructed below.
//! The remaining seed, `cc
//! 455d04f4a3339b26b238e09810662a5edaee813e25f4ca14b0cb6da1a2798a57`,
//! used the retired `PInputs` multi-binder representation; its non-isomorphic
//! replacement and explicit refusal are proved in `testkit/tests/ctor_engine.rs`.
//!
//! Historical receiver-specific method constructors are migrated to
//! `MethodCall(receiver, name, args)` by the complete executable manifest in
//! `testkit/src/corpus_migration.rs`. The old empty byte carrier
//! `CastBytes(ListLit([]))` and untagged empty path-map carrier are migrated to
//! their unique current forms, `CastBytes(BytesLit([]))` and mode-neutral
//! `Empty`. Every migrated test records both constructor trees.
//!
//! Root-level `NumLit` debug text erases whether its type was `BigInt`, `Int`,
//! or `UInt32`. No type is guessed: all three type-correct interpretations are
//! promoted independently. Each test constructs the typed term, compares its
//! canonicalized `Debug` output byte-for-byte with the applicable current
//! constructor tree, and exercises `Debug`, `Display`, `Clone`, and equality.
//!
//! Regenerate the reviewed snippets with:
//!
//! ```text
//! cargo run -p testkit --bin harvest_proptest_corpus -- \
//!     target/generated/rholang/rust_ctor.rs \
//!     languages/tests/gen_rholang_prop.proptest-regressions
//! ```

#![allow(clippy::needless_borrow)]

use mettail_languages::rholang::*;
use mettail_testkit::ctor::canonicalize_debug;

// ── Rholang — 54 corpus entries ──
// schema: target/generated/rholang/rust_ctor.rs
// corpus: languages/tests/gen_rholang_prop.proptest-regressions

/// Corpus entry 0 — seed `cc 03346dafed0ede2a05d17dae92d88bcbb31119f1787237777df2d0f4fa9ee2ee`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuoteShort(POutput2Plus(NQuoteShort(PathmapEmpty),
/// CastPathmap(PathmapLit(PathMapLit(HashMapLit({})))), [CastMap(MapLit(HashMapLit({})))]))
/// ```
///
/// Migrated to the current schema (0 method call(s), 0 byte carrier(s), 1 neutral path-map carrier(s)):
/// ```text
/// term = NQuoteShort(POutput2Plus(NQuoteShort(PathmapEmpty), CastPathmap(PathmapLit(Empty)),
/// [CastMap(MapLit(HashMapLit({})))]))
/// ```
#[test]
fn corpus_0_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuoteShort(std::sync::Arc::new(Proc::POutput2Plus(
        std::sync::Arc::new(Name::NQuoteShort(std::sync::Arc::new(Proc::PathmapEmpty))),
        std::sync::Arc::new(Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(
            mettail_runtime::PathMapLit::new(),
        )))),
        vec![Proc::CastMap(std::sync::Arc::new(Map::MapLit(
            mettail_runtime::HashMapLit::from_iter(vec![]),
        )))],
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuoteShort(POutput2Plus(NQuoteShort(PathmapEmpty), CastPathmap(PathmapLit(Empty)), [CastMap(MapLit(HashMapLit({})))]))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 1 — seed `cc 039a06c89511b661f1673b3fed5590361a0daa4f546630db6663644eb2194b5c`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuoteShort(PPar(HashBag { counts: {POutput(NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") }))), PZero): 1}, total_count: 1 }))
/// ```
#[test]
fn corpus_1_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuoteShort(std::sync::Arc::new(Proc::PPar(
        mettail_runtime::HashBag::from_iter(vec![Proc::POutput(
            std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )))),
            std::sync::Arc::new(Proc::PZero),
        )]),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuoteShort(PPar(HashBag { counts: {POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PZero): 1}, total_count: 1 }))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 2 — seed `cc 11e7b82d78e123ebe26de6bc87146b70a560dd039067319a347fd644abb9cb23`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(POutput2Plus(NParen(NQuoteNil), PNew(Scope { pattern: [Binder(FreeVar {
/// unique_id: UniqueId(1), pretty_name: Some("a0") }), Binder(FreeVar { unique_id: UniqueId(2),
/// pretty_name: Some("a1") })], body: PZero }), []))
/// ```
#[test]
fn corpus_2_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::POutput2Plus(
        std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NQuoteNil))),
        std::sync::Arc::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(
            vec![
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
            ],
            std::sync::Arc::new(Proc::PZero),
        ))),
        vec![],
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(POutput2Plus(NParen(NQuoteNil), PNew(Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") })], body: PZero }), []))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 3 — seed `cc 158eb7b9d551a69f3b398a8fed342b6affe49e465efdf95e2c0f2eea8c66a1c7`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PPar(HashBag { counts: {Err: 1, PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(94),
/// pretty_name: Some("a") }))): 1}, total_count: 2 })
/// ```
#[test]
fn corpus_3_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::PPar(mettail_runtime::HashBag::from_iter(vec![
        Proc::Err,
        Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
            mettail_runtime::get_or_create_var("a"),
        ))),
    ]));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PPar(HashBag { counts: {Err: 1, PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))): 1}, total_count: 2 })";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 4 — seed `cc 1726453d27fa34a9b20dac8010da343fbfe19abee6c42c868540e3858412393c`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = BitNot(POutput(NParen(NQuoteNil), POutput(NQuoteNil, PZero)))
/// ```
#[test]
fn corpus_4_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::BitNot(std::sync::Arc::new(Proc::POutput(
        std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NQuoteNil))),
        std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NQuoteNil),
            std::sync::Arc::new(Proc::PZero),
        )),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "BitNot(POutput(NParen(NQuoteNil), POutput(NQuoteNil, PZero)))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 5 — seed `cc 1a7cc34c8670538225596cfeb5921538019e7a380fe1b2fd5c8992a45c0fd98b`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = InputBindQuery(NQuote(Mul(MapEmpty, MapEmpty)), NQuote(Mul(MapEmpty, MapEmpty)),
/// [Mul(Mul(MapEmpty, MapEmpty), Mul(MapEmpty, MapEmpty))])
/// ```
#[test]
fn corpus_5_inputbind() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: InputBind = InputBind::InputBindQuery(
        std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::Mul(
            std::sync::Arc::new(Proc::MapEmpty),
            std::sync::Arc::new(Proc::MapEmpty),
        )))),
        std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::Mul(
            std::sync::Arc::new(Proc::MapEmpty),
            std::sync::Arc::new(Proc::MapEmpty),
        )))),
        vec![Proc::Mul(
            std::sync::Arc::new(Proc::Mul(
                std::sync::Arc::new(Proc::MapEmpty),
                std::sync::Arc::new(Proc::MapEmpty),
            )),
            std::sync::Arc::new(Proc::Mul(
                std::sync::Arc::new(Proc::MapEmpty),
                std::sync::Arc::new(Proc::MapEmpty),
            )),
        )],
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "InputBindQuery(NQuote(Mul(MapEmpty, MapEmpty)), NQuote(Mul(MapEmpty, MapEmpty)), [Mul(Mul(MapEmpty, MapEmpty), Mul(MapEmpty, MapEmpty))])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 6 — seed `cc 1ea68f081c51e379a565f624b67d7ea9fc8d1747574e51a4fb174706c8978a09`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = InputBindQuotedPersistent(LNth(POutputShort2Plus(PZero, PZero, [PZero, PZero]),
/// ToBool(PZero)), NQuote(NegProc(MapEmpty)))
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = InputBindQuotedPersistent(MethodCall(POutputShort2Plus(PZero, PZero, [PZero, PZero]),
/// "nth", [ToBool(PZero)]), NQuote(NegProc(MapEmpty)))
/// ```
#[test]
fn corpus_6_inputbind() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: InputBind = InputBind::InputBindQuotedPersistent(
        std::sync::Arc::new(Proc::MethodCall(
            std::sync::Arc::new(Proc::POutputShort2Plus(
                std::sync::Arc::new(Proc::PZero),
                std::sync::Arc::new(Proc::PZero),
                vec![Proc::PZero, Proc::PZero],
            )),
            std::string::String::from("nth"),
            vec![Proc::ToBool(std::sync::Arc::new(Proc::PZero))],
        )),
        std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::NegProc(std::sync::Arc::new(
            Proc::MapEmpty,
        ))))),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "InputBindQuotedPersistent(MethodCall(POutputShort2Plus(PZero, PZero, [PZero, PZero]), \"nth\", [ToBool(PZero)]), NQuote(NegProc(MapEmpty)))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 7 — seed `cc 2686dc3aafdd58aeac851b4a2631a7c413c35514d70592a666ddd5045d73ef82`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = POutput2Plus(NQuote(POutput(NQuoteNil, PZero)), PNew(Scope { pattern: [Binder(FreeVar
/// { unique_id: UniqueId(45), pretty_name: Some("a0") }), Binder(FreeVar { unique_id:
/// UniqueId(46), pretty_name: Some("a1") })], body: PZero }), [])
/// ```
#[test]
fn corpus_7_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::POutput2Plus(
        std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NQuoteNil),
            std::sync::Arc::new(Proc::PZero),
        )))),
        std::sync::Arc::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(
            vec![
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
            ],
            std::sync::Arc::new(Proc::PZero),
        ))),
        vec![],
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "POutput2Plus(NQuote(POutput(NQuoteNil, PZero)), PNew(Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") })], body: PZero }), [])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 8 — seed `cc 291081f6331884ee8da18a2ef67b64a54ee540915e585b5943c459f05a56c171`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = FractionProc(CastUInt32(BoolToUInt32(BoolLit(false))), POutput(NQuoteNil,
/// CastUInt32(NumLit(846790729))))
/// ```
#[test]
fn corpus_8_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::FractionProc(
        std::sync::Arc::new(Proc::CastUInt32(std::sync::Arc::new(UInt32::BoolToUInt32(
            std::sync::Arc::new(Bool::BoolLit(false)),
        )))),
        std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NQuoteNil),
            std::sync::Arc::new(Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(
                846790729u32,
            )))),
        )),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "FractionProc(CastUInt32(BoolToUInt32(BoolLit(false))), POutput(NQuoteNil, CastUInt32(NumLit(846790729))))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 9 — seed `cc 2fdc4c86795d3287dd70bfbded6f800e7fe91b30874101e048cff1424e4850a4`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = UIntBinProc(POutput2Plus(NParen(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(3),
/// pretty_name: Some("a") })))), POutput2Plus(NQuoteNil, PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(3), pretty_name: Some("a") }))), [PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(3), pretty_name: Some("a") })))]), [POutput2Plus(NQuoteNil,
/// PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(3), pretty_name: Some("a") }))),
/// [PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(3), pretty_name: Some("a") })))]),
/// UIntBinProc(PathmapEmpty, NumLit(8152392471429717442)), WZSetLeaf(PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(3), pretty_name: Some("a") }))), PathmapEmpty, PVar(OrdVar(Free(FreeVar
/// { unique_id: UniqueId(3), pretty_name: Some("a") }))))]),
/// UInt32ToInt(BoolToUInt32(BoolLit(false))))
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = UIntBinProc(POutput2Plus(NParen(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(3),
/// pretty_name: Some("a") })))), POutput2Plus(NQuoteNil, PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(3), pretty_name: Some("a") }))), [PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(3), pretty_name: Some("a") })))]), [POutput2Plus(NQuoteNil,
/// PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(3), pretty_name: Some("a") }))),
/// [PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(3), pretty_name: Some("a") })))]),
/// UIntBinProc(PathmapEmpty, NumLit(8152392471429717442)), MethodCall(PVar(OrdVar(Free(FreeVar
/// { unique_id: UniqueId(3), pretty_name: Some("a") }))), "setLeaf", [PathmapEmpty,
/// PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(3), pretty_name: Some("a") })))])]),
/// UInt32ToInt(BoolToUInt32(BoolLit(false))))
/// ```
#[test]
fn corpus_9_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::UIntBinProc(
        std::sync::Arc::new(Proc::POutput2Plus(
            std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NVar(
                mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                    mettail_runtime::get_or_create_var("a"),
                )),
            )))),
            std::sync::Arc::new(Proc::POutput2Plus(
                std::sync::Arc::new(Name::NQuoteNil),
                std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
                vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                    mettail_runtime::get_or_create_var("a"),
                )))],
            )),
            vec![
                Proc::POutput2Plus(
                    std::sync::Arc::new(Name::NQuoteNil),
                    std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    ))),
                    vec![Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    )))],
                ),
                Proc::UIntBinProc(
                    std::sync::Arc::new(Proc::PathmapEmpty),
                    std::sync::Arc::new(Int::NumLit(8152392471429717442i64)),
                ),
                Proc::MethodCall(
                    std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    ))),
                    std::string::String::from("setLeaf"),
                    vec![
                        Proc::PathmapEmpty,
                        Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                            mettail_runtime::get_or_create_var("a"),
                        ))),
                    ],
                ),
            ],
        )),
        std::sync::Arc::new(Int::UInt32ToInt(std::sync::Arc::new(UInt32::BoolToUInt32(
            std::sync::Arc::new(Bool::BoolLit(false)),
        )))),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "UIntBinProc(POutput2Plus(NParen(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), POutput2Plus(NQuoteNil, PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), [PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))]), [POutput2Plus(NQuoteNil, PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), [PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))]), UIntBinProc(PathmapEmpty, NumLit(8152392471429717442)), MethodCall(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), \"setLeaf\", [PathmapEmpty, PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))])]), UInt32ToInt(BoolToUInt32(BoolLit(false))))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 10 — seed `cc 382add9ea7f5ea86a01a400ac3cdc428ee0743e9850ef8979bfef2f7c3c58644`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = InputBind(NParen(NQuote(Err)), NQuoteNil)
/// ```
#[test]
fn corpus_10_inputbind() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: InputBind = InputBind::InputBind(
        std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(
            Proc::Err,
        ))))),
        std::sync::Arc::new(Name::NQuoteNil),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "InputBind(NParen(NQuote(Err)), NQuoteNil)";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 11 — seed `cc 385bc458d99f87a55c25a646754f7e39add86285529c966451cb01e7ae36d53c`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = ForRowWhere(InputBindQuoted(RZAscendOne(PZero), NQuoteNil),
/// [InputBindQuotedQuery(Not(PZero), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1224),
/// pretty_name: Some("a") }))), []), InputBindEmptyQuery(NQuoteShort(POutputNilEmpty),
/// [CastBool(BoolLit(false)), GtEq(MapEmpty, PPersistOutputNilEmpty)])], PZero)
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = ForRowWhere(InputBindQuoted(MethodCall(PZero, "ascendOne", []), NQuoteNil),
/// [InputBindQuotedQuery(Not(PZero), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1224),
/// pretty_name: Some("a") }))), []), InputBindEmptyQuery(NQuoteShort(POutputNilEmpty),
/// [CastBool(BoolLit(false)), GtEq(MapEmpty, PPersistOutputNilEmpty)])], PZero)
/// ```
#[test]
fn corpus_11_forrow() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: ForRow = ForRow::ForRowWhere(
        std::sync::Arc::new(InputBind::InputBindQuoted(
            std::sync::Arc::new(Proc::MethodCall(
                std::sync::Arc::new(Proc::PZero),
                std::string::String::from("ascendOne"),
                vec![],
            )),
            std::sync::Arc::new(Name::NQuoteNil),
        )),
        vec![
            InputBind::InputBindQuotedQuery(
                std::sync::Arc::new(Proc::Not(std::sync::Arc::new(Proc::PZero))),
                std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
                vec![],
            ),
            InputBind::InputBindEmptyQuery(
                std::sync::Arc::new(Name::NQuoteShort(std::sync::Arc::new(Proc::POutputNilEmpty))),
                vec![
                    Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(false))),
                    Proc::GtEq(
                        std::sync::Arc::new(Proc::MapEmpty),
                        std::sync::Arc::new(Proc::PPersistOutputNilEmpty),
                    ),
                ],
            ),
        ],
        std::sync::Arc::new(Proc::PZero),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "ForRowWhere(InputBindQuoted(MethodCall(PZero, \"ascendOne\", []), NQuoteNil), [InputBindQuotedQuery(Not(PZero), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), []), InputBindEmptyQuery(NQuoteShort(POutputNilEmpty), [CastBool(BoolLit(false)), GtEq(MapEmpty, PPersistOutputNilEmpty)])], PZero)";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 12 — seed `cc 3be0c67f04efea5640435662485454742a4a1b597cdd05ce35a3b4bdc75b1f46`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = POutput(NQuote(CastSet(SetLit(HashSetLit({})))), POutput(NQuote(MapEmpty),
/// POutput(NQuoteNil, MapEmpty)))
/// ```
#[test]
fn corpus_12_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::POutput(
        std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::CastSet(std::sync::Arc::new(
            Set::SetLit(mettail_runtime::HashSetLit::from_iter(vec![])),
        ))))),
        std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::MapEmpty))),
            std::sync::Arc::new(Proc::POutput(
                std::sync::Arc::new(Name::NQuoteNil),
                std::sync::Arc::new(Proc::MapEmpty),
            )),
        )),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "POutput(NQuote(CastSet(SetLit(HashSetLit({})))), POutput(NQuote(MapEmpty), POutput(NQuoteNil, MapEmpty)))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 13 — seed `cc 3f094e7afdaeb28822c9d41828f3ae134f5ad5049bc9f0d927bf9cc4c9666761`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(WZSetLeaf(PPar(HashBag { counts: {PZero: 1, PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(1), pretty_name: Some("a") }))): 1}, total_count: 2 }),
/// POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a") }))),
/// PZero), FractionProc(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name:
/// Some("a") }))), PZero)))
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = NQuote(MethodCall(PPar(HashBag { counts: {PZero: 1, PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(1), pretty_name: Some("a") }))): 1}, total_count: 2 }), "setLeaf",
/// [POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a") }))),
/// PZero), FractionProc(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name:
/// Some("a") }))), PZero)]))
/// ```
#[test]
fn corpus_13_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::MethodCall(
        std::sync::Arc::new(Proc::PPar(mettail_runtime::HashBag::from_iter(vec![
            Proc::PZero,
            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            ))),
        ]))),
        std::string::String::from("setLeaf"),
        vec![
            Proc::POutput(
                std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
                std::sync::Arc::new(Proc::PZero),
            ),
            Proc::FractionProc(
                std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
                std::sync::Arc::new(Proc::PZero),
            ),
        ],
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(MethodCall(PPar(HashBag { counts: {PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))): 1, PZero: 1}, total_count: 2 }), \"setLeaf\", [POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PZero), FractionProc(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PZero)]))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 14 — seed `cc 3f60980a5f271d72bfb7c3f1bd5edf15ec9d255a63dda67bbbed887d3162a309`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = InputBindQuery(NQuoteShort(CastFixed(FixedLit(Fixed(-855638016/1)))),
/// NQuoteShort(CastFixed(FixedLit(Fixed(-855638016/1)))), [])
/// ```
#[test]
fn corpus_14_inputbind() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: InputBind = InputBind::InputBindQuery(
        std::sync::Arc::new(Name::NQuoteShort(std::sync::Arc::new(Proc::CastFixed(
            std::sync::Arc::new(Fixed::FixedLit(mettail_runtime::CanonicalFixedPoint::new(
                num_bigint::BigInt::from(-855638016i64),
                0u32,
            ))),
        )))),
        std::sync::Arc::new(Name::NQuoteShort(std::sync::Arc::new(Proc::CastFixed(
            std::sync::Arc::new(Fixed::FixedLit(mettail_runtime::CanonicalFixedPoint::new(
                num_bigint::BigInt::from(-855638016i64),
                0u32,
            ))),
        )))),
        vec![],
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "InputBindQuery(NQuoteShort(CastFixed(FixedLit(Fixed(-855638016/1)))), NQuoteShort(CastFixed(FixedLit(Fixed(-855638016/1)))), [])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 16 — seed `cc 46cd9097509a704a72860e78805ba8742b02d1681d53a99670df3b8c67a76392`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(CastUInt32(NumLit(318881811)))
/// ```
#[test]
fn corpus_16_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::CastUInt32(std::sync::Arc::new(
        UInt32::NumLit(318881811u32),
    ))));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(CastUInt32(NumLit(318881811)))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 17 — seed `cc 4849f6a058be425ad0c8950ad5da85269eb69734b59cb9aa101ea258b946d602`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = InputBindQuotedQuery(POutput(NQuote(POutputNilEmpty), Err), NVar(OrdVar(Free(FreeVar
/// { unique_id: UniqueId(780), pretty_name: Some("a") }))), [])
/// ```
#[test]
fn corpus_17_inputbind() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: InputBind = InputBind::InputBindQuotedQuery(
        std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::POutputNilEmpty))),
            std::sync::Arc::new(Proc::Err),
        )),
        std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
            mettail_runtime::get_or_create_var("a"),
        )))),
        vec![],
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "InputBindQuotedQuery(POutput(NQuote(POutputNilEmpty), Err), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), [])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 18 — seed `cc 528a4a002581a89cf60acd697a8533741c48576c2061acec220932d0b4970e98`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = POutput(NQuoteNil, POutputShort(POutput(NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(4), pretty_name: Some("a") }))), PathmapEmpty), PPersistOutputNil(MapEmpty)))
/// ```
#[test]
fn corpus_18_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::POutput(
        std::sync::Arc::new(Name::NQuoteNil),
        std::sync::Arc::new(Proc::POutputShort(
            std::sync::Arc::new(Proc::POutput(
                std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
                std::sync::Arc::new(Proc::PathmapEmpty),
            )),
            std::sync::Arc::new(Proc::PPersistOutputNil(std::sync::Arc::new(Proc::MapEmpty))),
        )),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "POutput(NQuoteNil, POutputShort(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PathmapEmpty), PPersistOutputNil(MapEmpty)))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 19 — seed `cc 5ca53b06127ea50f939db0432af3452dec7ffa6d76ca6eae6681f55212a63ca5`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(IntBinProc(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(797),
/// pretty_name: Some("a") }))), PPersistOutputNilEmpty), NegInt(NumLit(1613346182411829711))))
/// ```
#[test]
fn corpus_19_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::IntBinProc(
        std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )))),
            std::sync::Arc::new(Proc::PPersistOutputNilEmpty),
        )),
        std::sync::Arc::new(Int::NegInt(std::sync::Arc::new(Int::NumLit(1613346182411829711i64)))),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(IntBinProc(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PPersistOutputNilEmpty), NegInt(NumLit(1613346182411829711))))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 20 — seed `cc 5dc592973c7b477c2fc3efd4fd180563b3c5187d566b0731fa63d4284d872762`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = ForRowWhere(InputBindPolyadic(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(127),
/// pretty_name: Some("a") }))), [NQuoteNil, NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(127), pretty_name: Some("a") })))], NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(127), pretty_name: Some("a") })))), [InputBindQuery(NQuoteNil,
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(127), pretty_name: Some("a") }))), [PZero,
/// MSize(PZero)]), InputBindPolyadic(NQuote(POutputNilEmpty), [NQuote(POutputNilEmpty),
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(127), pretty_name: Some("a") })))],
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(127), pretty_name: Some("a") }))))],
/// PPersistOutput2Plus(NQuoteNil, FloatBinProc(PZero, NumLit(3314650748809248789)), []))
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = ForRowWhere(InputBindPolyadic(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(127),
/// pretty_name: Some("a") }))), [NQuoteNil, NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(127), pretty_name: Some("a") })))], NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(127), pretty_name: Some("a") })))), [InputBindQuery(NQuoteNil,
/// NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(127), pretty_name: Some("a") }))), [PZero,
/// MethodCall(PZero, "size", [])]), InputBindPolyadic(NQuote(POutputNilEmpty),
/// [NQuote(POutputNilEmpty), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(127), pretty_name:
/// Some("a") })))], NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(127), pretty_name: Some("a")
/// }))))], PPersistOutput2Plus(NQuoteNil, FloatBinProc(PZero, NumLit(3314650748809248789)),
/// []))
/// ```
#[test]
fn corpus_20_forrow() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: ForRow = ForRow::ForRowWhere(
        std::sync::Arc::new(InputBind::InputBindPolyadic(
            std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )))),
            vec![
                Name::NQuoteNil,
                Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                    mettail_runtime::get_or_create_var("a"),
                ))),
            ],
            std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )))),
        )),
        vec![
            InputBind::InputBindQuery(
                std::sync::Arc::new(Name::NQuoteNil),
                std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
                vec![
                    Proc::PZero,
                    Proc::MethodCall(
                        std::sync::Arc::new(Proc::PZero),
                        std::string::String::from("size"),
                        vec![],
                    ),
                ],
            ),
            InputBind::InputBindPolyadic(
                std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::POutputNilEmpty))),
                vec![
                    Name::NQuote(std::sync::Arc::new(Proc::POutputNilEmpty)),
                    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                ],
                std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
            ),
        ],
        std::sync::Arc::new(Proc::PPersistOutput2Plus(
            std::sync::Arc::new(Name::NQuoteNil),
            std::sync::Arc::new(Proc::FloatBinProc(
                std::sync::Arc::new(Proc::PZero),
                std::sync::Arc::new(Int::NumLit(3314650748809248789i64)),
            )),
            vec![],
        )),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "ForRowWhere(InputBindPolyadic(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), [NQuoteNil, NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), [InputBindQuery(NQuoteNil, NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), [PZero, MethodCall(PZero, \"size\", [])]), InputBindPolyadic(NQuote(POutputNilEmpty), [NQuote(POutputNilEmpty), NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))], PPersistOutput2Plus(NQuoteNil, FloatBinProc(PZero, NumLit(3314650748809248789)), []))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 21 — seed `cc 5f06b23eb0e1656173613b44cf9aac975aeacda99d0014f1a47ea608fba0e916`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = ForRowSingleNoWhere(InputBindEmptyQuery(NQuoteNil, [CastSet(SetLit(HashSetLit({}))),
/// PPersistOutputEmpty(NQuoteNil)]))
/// ```
#[test]
fn corpus_21_forrow() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: ForRow =
        ForRow::ForRowSingleNoWhere(std::sync::Arc::new(InputBind::InputBindEmptyQuery(
            std::sync::Arc::new(Name::NQuoteNil),
            vec![
                Proc::CastSet(std::sync::Arc::new(Set::SetLit(
                    mettail_runtime::HashSetLit::from_iter(vec![]),
                ))),
                Proc::PPersistOutputEmpty(std::sync::Arc::new(Name::NQuoteNil)),
            ],
        )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "ForRowSingleNoWhere(InputBindEmptyQuery(NQuoteNil, [CastSet(SetLit(HashSetLit({}))), PPersistOutputEmpty(NQuoteNil)]))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 22 — seed `cc 6351fa0bd4bd57621beff076d618aff3a3530b03e58ba678737ac47c8da0a615`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = InputBindQuotedPersistent(POutput2Plus(NParen(NQuoteNil),
/// CastPathmap(PathmapLit(PathMapLit(HashMapLit({})))), []), NQuoteNil)
/// ```
///
/// Migrated to the current schema (0 method call(s), 0 byte carrier(s), 1 neutral path-map carrier(s)):
/// ```text
/// term = InputBindQuotedPersistent(POutput2Plus(NParen(NQuoteNil),
/// CastPathmap(PathmapLit(Empty)), []), NQuoteNil)
/// ```
#[test]
fn corpus_22_inputbind() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: InputBind = InputBind::InputBindQuotedPersistent(
        std::sync::Arc::new(Proc::POutput2Plus(
            std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NQuoteNil))),
            std::sync::Arc::new(Proc::CastPathmap(std::sync::Arc::new(Pathmap::PathmapLit(
                mettail_runtime::PathMapLit::new(),
            )))),
            vec![],
        )),
        std::sync::Arc::new(Name::NQuoteNil),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "InputBindQuotedPersistent(POutput2Plus(NParen(NQuoteNil), CastPathmap(PathmapLit(Empty)), []), NQuoteNil)";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 23 — seed `cc 681d60d86b87a32a1daf099097a929afd50c77670e738afad42b8319ac1b839e`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = POutputShort2Plus(MSet(NegProc(Err), POutput(NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(77), pretty_name: Some("a") }))), PZero), PZero), PZero, [])
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = POutputShort2Plus(MethodCall(NegProc(Err), "set", [POutput(NVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(77), pretty_name: Some("a") }))), PZero), PZero]), PZero, [])
/// ```
#[test]
fn corpus_23_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::POutputShort2Plus(
        std::sync::Arc::new(Proc::MethodCall(
            std::sync::Arc::new(Proc::NegProc(std::sync::Arc::new(Proc::Err))),
            std::string::String::from("set"),
            vec![
                Proc::POutput(
                    std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    ))),
                    std::sync::Arc::new(Proc::PZero),
                ),
                Proc::PZero,
            ],
        )),
        std::sync::Arc::new(Proc::PZero),
        vec![],
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "POutputShort2Plus(MethodCall(NegProc(Err), \"set\", [POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PZero), PZero]), PZero, [])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 24 — seed `cc 6d3cb929c00deff18eab1ab47c17c2e3f8221934408a27ae076591518171c20c`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = POutput2Plus(NParen(NQuoteShort(Err)), CastFixed(FixedLit(Fixed(-2147483648/1))),
/// [MSize(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a")
/// }))), PZero)), CastBigRat(IntToBigRat(NumLit(967646845041)))])
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = POutput2Plus(NParen(NQuoteShort(Err)), CastFixed(FixedLit(Fixed(-2147483648/1))),
/// [MethodCall(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a") }))), PZero), "size", []), CastBigRat(IntToBigRat(NumLit(967646845041)))])
/// ```
#[test]
fn corpus_24_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::POutput2Plus(
        std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NQuoteShort(
            std::sync::Arc::new(Proc::Err),
        )))),
        std::sync::Arc::new(Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(
            mettail_runtime::CanonicalFixedPoint::new(
                num_bigint::BigInt::from(-2147483648i64),
                0u32,
            ),
        )))),
        vec![
            Proc::MethodCall(
                std::sync::Arc::new(Proc::POutput(
                    std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    ))),
                    std::sync::Arc::new(Proc::PZero),
                )),
                std::string::String::from("size"),
                vec![],
            ),
            Proc::CastBigRat(std::sync::Arc::new(BigRat::IntToBigRat(std::sync::Arc::new(
                Int::NumLit(967646845041i64),
            )))),
        ],
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "POutput2Plus(NParen(NQuoteShort(Err)), CastFixed(FixedLit(Fixed(-2147483648/1))), [MethodCall(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PZero), \"size\", []), CastBigRat(IntToBigRat(NumLit(967646845041)))])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 25 — seed `cc 81fdf83bbc0525527f4422b31710a7cd6d48998605c18ecb6da076ab9fb1689b`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PParInfix(CastInt(NegInt(NumLit(0))), POutput(NParen(NQuoteNil), PZero))
/// ```
#[test]
fn corpus_25_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::PParInfix(
        std::sync::Arc::new(Proc::CastInt(std::sync::Arc::new(Int::NegInt(std::sync::Arc::new(
            Int::NumLit(0i64),
        ))))),
        std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NQuoteNil))),
            std::sync::Arc::new(Proc::PZero),
        )),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "PParInfix(CastInt(NegInt(NumLit(0))), POutput(NParen(NQuoteNil), PZero))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 26 — seed `cc 8539fd7e0cc7e3592dd9d857c8eada7d26773bbf3396027c1e7a12ded50d6f00`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = MSet(PGetSubtrie(IntBinProc(PZero, NumLit(0))), PParInfix(PForUser([], PZero),
/// POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a") }))),
/// MapEmpty)), IntBinProc(PZero, NumLit(792633534417207296)))
/// ```
///
/// Migrated to the current schema (2 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = MethodCall(MethodCall(IntBinProc(PZero, NumLit(0)), "getSubtrie", []), "set",
/// [PParInfix(PForUser([], PZero), POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") }))), MapEmpty)), IntBinProc(PZero, NumLit(792633534417207296))])
/// ```
#[test]
fn corpus_26_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::MethodCall(
        std::sync::Arc::new(Proc::MethodCall(
            std::sync::Arc::new(Proc::IntBinProc(
                std::sync::Arc::new(Proc::PZero),
                std::sync::Arc::new(Int::NumLit(0i64)),
            )),
            std::string::String::from("getSubtrie"),
            vec![],
        )),
        std::string::String::from("set"),
        vec![
            Proc::PParInfix(
                std::sync::Arc::new(Proc::PForUser(vec![], std::sync::Arc::new(Proc::PZero))),
                std::sync::Arc::new(Proc::POutput(
                    std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                    ))),
                    std::sync::Arc::new(Proc::MapEmpty),
                )),
            ),
            Proc::IntBinProc(
                std::sync::Arc::new(Proc::PZero),
                std::sync::Arc::new(Int::NumLit(792633534417207296i64)),
            ),
        ],
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "MethodCall(MethodCall(IntBinProc(PZero, NumLit(0)), \"getSubtrie\", []), \"set\", [PParInfix(PForUser([], PZero), POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), MapEmpty)), IntBinProc(PZero, NumLit(792633534417207296))])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 27 — seed `cc 8a7690081f679a66ff7a676fd568699397c22c0a66ceefc4044387f20a60f6d1`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = InputBindEmptyQuery(NQuote(POutputNilEmpty), [])
/// ```
#[test]
fn corpus_27_inputbind() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: InputBind = InputBind::InputBindEmptyQuery(
        std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::POutputNilEmpty))),
        vec![],
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "InputBindEmptyQuery(NQuote(POutputNilEmpty), [])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 28 — seed `cc 9987ac0377201e9c91878fa79c18fc00400e609af2116f0d385876dc510c84a0`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = PMeet(LNth(POutputQuotedEmpty(NQuoteNil), POutput(NVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(1), pretty_name: Some("a") }))), PZero)), PZero)
/// ```
///
/// Migrated to the current schema (2 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = MethodCall(MethodCall(POutputQuotedEmpty(NQuoteNil), "nth",
/// [POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a") }))),
/// PZero)]), "meet", [PZero])
/// ```
#[test]
fn corpus_28_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::MethodCall(
        std::sync::Arc::new(Proc::MethodCall(
            std::sync::Arc::new(Proc::POutputQuotedEmpty(std::sync::Arc::new(Name::NQuoteNil))),
            std::string::String::from("nth"),
            vec![Proc::POutput(
                std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
                std::sync::Arc::new(Proc::PZero),
            )],
        )),
        std::string::String::from("meet"),
        vec![Proc::PZero],
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "MethodCall(MethodCall(POutputQuotedEmpty(NQuoteNil), \"nth\", [POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PZero)]), \"meet\", [PZero])";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 29 — seed `cc 9b8d92b24169e1e1b894afece11865a36e02f086d852f11036ab75cd395db1a4`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(LtEq(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a") }))), PZero), POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") }))), PZero)))
/// ```
#[test]
fn corpus_29_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::LtEq(
        std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )))),
            std::sync::Arc::new(Proc::PZero),
        )),
        std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )))),
            std::sync::Arc::new(Proc::PZero),
        )),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(LtEq(POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PZero), POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PZero)))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 30 — seed `cc a293b4367ab74525c2de717889912c366bb271e669bcb2499e414bc2d00691cb`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(POutput2Plus(NQuoteNil, CastList(ListLit([])), [BigratCastProc(MapEmpty),
/// RZAscendOne(PZero)]))
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = NQuote(POutput2Plus(NQuoteNil, CastList(ListLit([])), [BigratCastProc(MapEmpty),
/// MethodCall(PZero, "ascendOne", [])]))
/// ```
#[test]
fn corpus_30_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::POutput2Plus(
        std::sync::Arc::new(Name::NQuoteNil),
        std::sync::Arc::new(Proc::CastList(std::sync::Arc::new(List::ListLit(vec![])))),
        vec![
            Proc::BigratCastProc(std::sync::Arc::new(Proc::MapEmpty)),
            Proc::MethodCall(
                std::sync::Arc::new(Proc::PZero),
                std::string::String::from("ascendOne"),
                vec![],
            ),
        ],
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(POutput2Plus(NQuoteNil, CastList(ListLit([])), [BigratCastProc(MapEmpty), MethodCall(PZero, \"ascendOne\", [])]))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 31 — seed `cc a92be7635c16495126caeb043f1793c5caa9191c9f66a0ea5a58df54187e2c08`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = BitOr(NegProc(WZRemoveLeaf(PZero)), POutput(NParen(NQuoteNil),
/// NegProc(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a") }))))))
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = BitOr(NegProc(MethodCall(PZero, "removeLeaf", [])), POutput(NParen(NQuoteNil),
/// NegProc(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name: Some("a") }))))))
/// ```
#[test]
fn corpus_31_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::BitOr(
        std::sync::Arc::new(Proc::NegProc(std::sync::Arc::new(Proc::MethodCall(
            std::sync::Arc::new(Proc::PZero),
            std::string::String::from("removeLeaf"),
            vec![],
        )))),
        std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NQuoteNil))),
            std::sync::Arc::new(Proc::NegProc(std::sync::Arc::new(Proc::PVar(
                mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                    mettail_runtime::get_or_create_var("a"),
                )),
            )))),
        )),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "BitOr(NegProc(MethodCall(PZero, \"removeLeaf\", [])), POutput(NParen(NQuoteNil), NegProc(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 32 — seed `cc a98e28482ce179f938523a753b8230fcc908ef30875d070ed37a0817b0dbfc97`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = CastInt(NumLit(2160916369174765053))
/// ```
#[test]
fn corpus_32_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::CastInt(std::sync::Arc::new(Int::NumLit(2160916369174765053i64)));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "CastInt(NumLit(2160916369174765053))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 33 — seed `cc b1c422685c88bfb74a4f18ff86070093effe9c8a049dd99067bea9e46ed485cd`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = CastBigInt(NumLit(1393251083))
/// ```
#[test]
fn corpus_33_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(
        mettail_runtime::CanonicalBigInt::from(num_bigint::BigInt::from(1393251083i64)),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "CastBigInt(NumLit(1393251083))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 34 — seed `cc b381e12c138cae552714b60d6de693abf958a1f9b8bc025b7883df2bfb02d38a`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuoteShort(PPersistOutput2Plus(NQuoteShort(MapEmpty), PPersistOutput2Plus(NQuoteNil,
/// MapEmpty, []), []))
/// ```
#[test]
fn corpus_34_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuoteShort(std::sync::Arc::new(Proc::PPersistOutput2Plus(
        std::sync::Arc::new(Name::NQuoteShort(std::sync::Arc::new(Proc::MapEmpty))),
        std::sync::Arc::new(Proc::PPersistOutput2Plus(
            std::sync::Arc::new(Name::NQuoteNil),
            std::sync::Arc::new(Proc::MapEmpty),
            vec![],
        )),
        vec![],
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuoteShort(PPersistOutput2Plus(NQuoteShort(MapEmpty), PPersistOutput2Plus(NQuoteNil, MapEmpty, []), []))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 35 — seed `cc b3ba427429a5f16f31770c94b1dc4e99476c3b236fa7428b6a42ff7ed270d24c`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(IntBinProc(POutputEmpty(NQuoteNil), UInt32ToInt(NumLit(3822638370))))
/// ```
#[test]
fn corpus_35_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::IntBinProc(
        std::sync::Arc::new(Proc::POutputEmpty(std::sync::Arc::new(Name::NQuoteNil))),
        std::sync::Arc::new(Int::UInt32ToInt(std::sync::Arc::new(UInt32::NumLit(3822638370u32)))),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(IntBinProc(POutputEmpty(NQuoteNil), UInt32ToInt(NumLit(3822638370))))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 36 — seed `cc b5b31efeaa6f3b927c744abba4153bfcb5d80dbe8599288694eca65998a33d11`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = InputBind(NQuote(CastList(ListLit([]))), NQuoteShort(WZJoinInto(MapEmpty,
/// PathmapEmpty)))
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = InputBind(NQuote(CastList(ListLit([]))), NQuoteShort(MethodCall(MapEmpty, "joinInto",
/// [PathmapEmpty])))
/// ```
#[test]
fn corpus_36_inputbind() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: InputBind = InputBind::InputBind(
        std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::CastList(
            std::sync::Arc::new(List::ListLit(vec![])),
        )))),
        std::sync::Arc::new(Name::NQuoteShort(std::sync::Arc::new(Proc::MethodCall(
            std::sync::Arc::new(Proc::MapEmpty),
            std::string::String::from("joinInto"),
            vec![Proc::PathmapEmpty],
        )))),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "InputBind(NQuote(CastList(ListLit([]))), NQuoteShort(MethodCall(MapEmpty, \"joinInto\", [PathmapEmpty])))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 37 — seed `cc b996675ed0c7a7a670a0687e39d3d368bf0da05104ed547d5fdbd33e05e2326f`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = BitNot(PZero)
/// ```
#[test]
fn corpus_37_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::BitNot(std::sync::Arc::new(Proc::PZero));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "BitNot(PZero)";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 38 — seed `cc c78da8380113f4ea7d1f4b8e466e456f3dbbd3550f787b965171f3602ec8ac3d`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = Not(POutputQuoted(NQuote(POutputNilEmpty), Not(Err)))
/// ```
#[test]
fn corpus_38_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::Not(std::sync::Arc::new(Proc::POutputQuoted(
        std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::POutputNilEmpty))),
        std::sync::Arc::new(Proc::Not(std::sync::Arc::new(Proc::Err))),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "Not(POutputQuoted(NQuote(POutputNilEmpty), Not(Err)))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 39 — seed `cc ca9f298056e019ffcf7b25c2773d154d0ed594265172fc39cc6e4a5ec610253d`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = InputBindPolyadic(NQuoteShort(PNew(Scope { pattern: [Binder(FreeVar { unique_id:
/// UniqueId(2), pretty_name: Some("a0") }), Binder(FreeVar { unique_id: UniqueId(4),
/// pretty_name: Some("a1") })], body: PZero })), [], NQuoteNil)
/// ```
#[test]
fn corpus_39_inputbind() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: InputBind = InputBind::InputBindPolyadic(
        std::sync::Arc::new(Name::NQuoteShort(std::sync::Arc::new(Proc::PNew(
            mettail_runtime::Scope::from_parts_unsafe(
                vec![
                    mettail_runtime::Binder(mettail_runtime::get_or_create_var("a0")),
                    mettail_runtime::Binder(mettail_runtime::get_or_create_var("a1")),
                ],
                std::sync::Arc::new(Proc::PZero),
            ),
        )))),
        vec![],
        std::sync::Arc::new(Name::NQuoteNil),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "InputBindPolyadic(NQuoteShort(PNew(Scope { pattern: [Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a0\") }), Binder(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a1\") })], body: PZero })), [], NQuoteNil)";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 40 — seed `cc d0714a588a685641f38e732b430880ee7081aaa2d1258804ca221bf9a8ae2289`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = InputBindPersistent(NQuote(Lt(PPersistOutputNilEmpty, PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a") }))))), NQuote(Lt(MapEmpty,
/// PPersistOutputNilEmpty)))
/// ```
#[test]
fn corpus_40_inputbind() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: InputBind = InputBind::InputBindPersistent(
        std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::Lt(
            std::sync::Arc::new(Proc::PPersistOutputNilEmpty),
            std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )))),
        )))),
        std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::Lt(
            std::sync::Arc::new(Proc::MapEmpty),
            std::sync::Arc::new(Proc::PPersistOutputNilEmpty),
        )))),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "InputBindPersistent(NQuote(Lt(PPersistOutputNilEmpty, PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))), NQuote(Lt(MapEmpty, PPersistOutputNilEmpty)))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 41 — seed `cc d0996c5897a6ca66c401d176f63e6abeeb41a2778f522a3871dcc52804a17f68`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(Eq(PDrop(NQuoteNil), PZero))
/// ```
#[test]
fn corpus_41_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::Eq(
        std::sync::Arc::new(Proc::PDrop(std::sync::Arc::new(Name::NQuoteNil))),
        std::sync::Arc::new(Proc::PZero),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(Eq(PDrop(NQuoteNil), PZero))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 42 — seed `cc d0c9823918d12a13891b15bf8be8d62e6774ac84dd4678b9874b569e24a9c323`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = IntBinProc(GtEq(GtEq(PZero, PZero), LtEq(PPersistOutputNilEmpty, PathmapEmpty)),
/// NegInt(UInt32ToInt(NumLit(2905357887))))
/// ```
#[test]
fn corpus_42_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::IntBinProc(
        std::sync::Arc::new(Proc::GtEq(
            std::sync::Arc::new(Proc::GtEq(
                std::sync::Arc::new(Proc::PZero),
                std::sync::Arc::new(Proc::PZero),
            )),
            std::sync::Arc::new(Proc::LtEq(
                std::sync::Arc::new(Proc::PPersistOutputNilEmpty),
                std::sync::Arc::new(Proc::PathmapEmpty),
            )),
        )),
        std::sync::Arc::new(Int::NegInt(std::sync::Arc::new(Int::UInt32ToInt(
            std::sync::Arc::new(UInt32::NumLit(2905357887u32)),
        )))),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "IntBinProc(GtEq(GtEq(PZero, PZero), LtEq(PPersistOutputNilEmpty, PathmapEmpty)), NegInt(UInt32ToInt(NumLit(2905357887))))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 43 — seed `cc d29e4ed1d77b970043aaa97b1356cd06237bab05d29cd1d4fb0f9b102c3ca206`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = IntBinProc(POutputShort(CastBool(BoolLit(false)), PZero), NumLit(2498927616))
/// ```
#[test]
fn corpus_43_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::IntBinProc(
        std::sync::Arc::new(Proc::POutputShort(
            std::sync::Arc::new(Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(false)))),
            std::sync::Arc::new(Proc::PZero),
        )),
        std::sync::Arc::new(Int::NumLit(2498927616i64)),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "IntBinProc(POutputShort(CastBool(BoolLit(false)), PZero), NumLit(2498927616))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 44 — seed `cc d5d2383d2b208ff0250cc4d98b9fe30eb020f0d7403c3fd59cd45172abcfbc73`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(PForUser([ForRowNoWhere(IVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a") }))), [])], BDiff(MapEmpty, Err)))
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = NQuote(PForUser([ForRowNoWhere(IVar(OrdVar(Free(FreeVar { unique_id: UniqueId(1),
/// pretty_name: Some("a") }))), [])], MethodCall(MapEmpty, "diff", [Err])))
/// ```
#[test]
fn corpus_44_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::PForUser(
        vec![ForRow::ForRowNoWhere(
            std::sync::Arc::new(InputBind::IVar(mettail_runtime::OrdVar(
                mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
            ))),
            vec![],
        )],
        std::sync::Arc::new(Proc::MethodCall(
            std::sync::Arc::new(Proc::MapEmpty),
            std::string::String::from("diff"),
            vec![Proc::Err],
        )),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(PForUser([ForRowNoWhere(IVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), [])], MethodCall(MapEmpty, \"diff\", [Err])))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 45 — seed `cc dc0f824e280bcdf6ca74dacb4e4ffd734d39330098950c3a5baaf7be1a83cf66`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = ForRowSingleNoWhere(InputBindQuery(NParen(NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(788), pretty_name: Some("a") })))), NParen(NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(788), pretty_name: Some("a") })))), [Not(MapEmpty)]))
/// ```
#[test]
fn corpus_45_forrow() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: ForRow = ForRow::ForRowSingleNoWhere(std::sync::Arc::new(InputBind::InputBindQuery(
        std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NVar(
            mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )),
        )))),
        std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NVar(
            mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )),
        )))),
        vec![Proc::Not(std::sync::Arc::new(Proc::MapEmpty))],
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "ForRowSingleNoWhere(InputBindQuery(NParen(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), NParen(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), [Not(MapEmpty)]))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 46 — seed `cc e212e5533f5d85db728095d6e0f475c04d3d25341dabea7bd6de90a5968df755`.
///
/// The erased root type admits 3 exact interpretations: BigInt, Int, UInt32. This test promotes the `BigInt` interpretation; every other type-correct interpretation is promoted by its own sibling test.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NumLit(488447261)
/// ```
#[test]
fn corpus_46_bigint() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: BigInt = BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(
        num_bigint::BigInt::from(488447261i64),
    ));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NumLit(488447261)";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 46 — seed `cc e212e5533f5d85db728095d6e0f475c04d3d25341dabea7bd6de90a5968df755`.
///
/// The erased root type admits 3 exact interpretations: BigInt, Int, UInt32. This test promotes the `Int` interpretation; every other type-correct interpretation is promoted by its own sibling test.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NumLit(488447261)
/// ```
#[test]
fn corpus_46_int() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Int = Int::NumLit(488447261i64);

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NumLit(488447261)";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 46 — seed `cc e212e5533f5d85db728095d6e0f475c04d3d25341dabea7bd6de90a5968df755`.
///
/// The erased root type admits 3 exact interpretations: BigInt, Int, UInt32. This test promotes the `UInt32` interpretation; every other type-correct interpretation is promoted by its own sibling test.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NumLit(488447261)
/// ```
#[test]
fn corpus_46_uint32() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: UInt32 = UInt32::NumLit(488447261u32);

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NumLit(488447261)";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 47 — seed `cc e30600258f8e442dcde12fb315ad527ae50948f1ccf091a45bf440d77169e273`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = Or(BigintCastProc(KeysMap(PZero)), POutput(NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") }))), KeysMap(PZero)))
/// ```
///
/// Migrated to the current schema (2 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = Or(BigintCastProc(MethodCall(PZero, "keys", [])), POutput(NVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a") }))), MethodCall(PZero, "keys", [])))
/// ```
#[test]
fn corpus_47_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::Or(
        std::sync::Arc::new(Proc::BigintCastProc(std::sync::Arc::new(Proc::MethodCall(
            std::sync::Arc::new(Proc::PZero),
            std::string::String::from("keys"),
            vec![],
        )))),
        std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )))),
            std::sync::Arc::new(Proc::MethodCall(
                std::sync::Arc::new(Proc::PZero),
                std::string::String::from("keys"),
                vec![],
            )),
        )),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "Or(BigintCastProc(MethodCall(PZero, \"keys\", [])), POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), MethodCall(PZero, \"keys\", [])))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 48 — seed `cc e37b9bae7def93860e808aac4e3bea6dc5e7382f4e156a792b9da582aff6670e`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = POutput(NQuoteShort(PParInfix(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") }))), PathmapEmpty)), PParInfix(CastUInt32(NumLit(405349895)),
/// POutput(NQuoteNil, Err)))
/// ```
#[test]
fn corpus_48_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::POutput(
        std::sync::Arc::new(Name::NQuoteShort(std::sync::Arc::new(Proc::PParInfix(
            std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )))),
            std::sync::Arc::new(Proc::PathmapEmpty),
        )))),
        std::sync::Arc::new(Proc::PParInfix(
            std::sync::Arc::new(Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(
                405349895u32,
            )))),
            std::sync::Arc::new(Proc::POutput(
                std::sync::Arc::new(Name::NQuoteNil),
                std::sync::Arc::new(Proc::Err),
            )),
        )),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "POutput(NQuoteShort(PParInfix(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PathmapEmpty)), PParInfix(CastUInt32(NumLit(405349895)), POutput(NQuoteNil, Err)))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 49 — seed `cc eabf9162d1f425d1fdc21cf3802812dae47ecac6f9382a56f222c2aa49a5454e`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = And(Or(PPersistOutputShort(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(9),
/// pretty_name: Some("a") }))), PZero), CastList(ListLit([]))), And(Or(PathmapEmpty,
/// PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(9), pretty_name: Some("a") })))),
/// PForUser([FVar(OrdVar(Free(FreeVar { unique_id: UniqueId(9), pretty_name: Some("a") }))),
/// FVar(OrdVar(Free(FreeVar { unique_id: UniqueId(9), pretty_name: Some("a") }))),
/// FVar(OrdVar(Free(FreeVar { unique_id: UniqueId(9), pretty_name: Some("a") })))],
/// PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(9), pretty_name: Some("a") }))))))
/// ```
#[test]
fn corpus_49_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::And(
        std::sync::Arc::new(Proc::Or(
            std::sync::Arc::new(Proc::PPersistOutputShort(
                std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
                std::sync::Arc::new(Proc::PZero),
            )),
            std::sync::Arc::new(Proc::CastList(std::sync::Arc::new(List::ListLit(vec![])))),
        )),
        std::sync::Arc::new(Proc::And(
            std::sync::Arc::new(Proc::Or(
                std::sync::Arc::new(Proc::PathmapEmpty),
                std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
            )),
            std::sync::Arc::new(Proc::PForUser(
                vec![
                    ForRow::FVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    ForRow::FVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                    ForRow::FVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                        mettail_runtime::get_or_create_var("a"),
                    ))),
                ],
                std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(
                    mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
                ))),
            )),
        )),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "And(Or(PPersistOutputShort(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PZero), CastList(ListLit([]))), And(Or(PathmapEmpty, PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), PForUser([FVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), FVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), FVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))], PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 50 — seed `cc efb4d761385d14d957e6d5f4ba3aa98458685c55cfb45291e77e3596112937d8`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(POutput(NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(344),
/// pretty_name: Some("a") })))), POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(344),
/// pretty_name: Some("a") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(344),
/// pretty_name: Some("a") }))))))
/// ```
#[test]
fn corpus_50_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::POutput(
        std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PVar(
            mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )),
        )))),
        std::sync::Arc::new(Proc::POutput(
            std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )))),
            std::sync::Arc::new(Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )))),
        )),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(POutput(NQuote(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), POutput(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 51 — seed `cc f0bf93cdd672abf4cb40a4217fe9dcf443f9ef53ef074b774367b979df62f321`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = ForRowWhere(InputBindPolyadic(NParen(NQuoteNil), [NQuoteShort(MapEmpty)],
/// NParen(NQuoteNil)), [], MValues(FixedBinProc(POutputNilEmpty, NumLit(6967741428829650031))))
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = ForRowWhere(InputBindPolyadic(NParen(NQuoteNil), [NQuoteShort(MapEmpty)],
/// NParen(NQuoteNil)), [], MethodCall(FixedBinProc(POutputNilEmpty,
/// NumLit(6967741428829650031)), "values", []))
/// ```
#[test]
fn corpus_51_forrow() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: ForRow = ForRow::ForRowWhere(
        std::sync::Arc::new(InputBind::InputBindPolyadic(
            std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NQuoteNil))),
            vec![Name::NQuoteShort(std::sync::Arc::new(Proc::MapEmpty))],
            std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NQuoteNil))),
        )),
        vec![],
        std::sync::Arc::new(Proc::MethodCall(
            std::sync::Arc::new(Proc::FixedBinProc(
                std::sync::Arc::new(Proc::POutputNilEmpty),
                std::sync::Arc::new(Int::NumLit(6967741428829650031i64)),
            )),
            std::string::String::from("values"),
            vec![],
        )),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "ForRowWhere(InputBindPolyadic(NParen(NQuoteNil), [NQuoteShort(MapEmpty)], NParen(NQuoteNil)), [], MethodCall(FixedBinProc(POutputNilEmpty, NumLit(6967741428829650031)), \"values\", []))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 52 — seed `cc fab2ff51109b347a62d722e563e0e17845ebf423de6f86d260b7611451e42394`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NQuote(MGet(NegProc(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name:
/// Some("a") })))), PZero))
/// ```
///
/// Migrated to the current schema (1 method call(s), 0 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = NQuote(MethodCall(NegProc(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0),
/// pretty_name: Some("a") })))), "get", [PZero]))
/// ```
#[test]
fn corpus_52_name() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Name = Name::NQuote(std::sync::Arc::new(Proc::MethodCall(
        std::sync::Arc::new(Proc::NegProc(std::sync::Arc::new(Proc::PVar(
            mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )),
        )))),
        std::string::String::from("get"),
        vec![Proc::PZero],
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "NQuote(MethodCall(NegProc(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), \"get\", [PZero]))";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}

/// Corpus entry 53 — seed `cc 30b5c23acd4ab5b6c55dae27d3ffb297c8bde6228026b9d38a59990898fa1369`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = InputBindPolyadic(NQuoteNil, [NParen(NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") })))), NQuote(CastBytes(ListLit([])))], NQuoteNil)
/// ```
///
/// Migrated to the current schema (0 method call(s), 1 byte carrier(s), 0 neutral path-map carrier(s)):
/// ```text
/// term = InputBindPolyadic(NQuoteNil, [NParen(NVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(0), pretty_name: Some("a") })))), NQuote(CastBytes(BytesLit([])))], NQuoteNil)
/// ```
#[test]
fn corpus_53_inputbind() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: InputBind = InputBind::InputBindPolyadic(
        std::sync::Arc::new(Name::NQuoteNil),
        vec![
            Name::NParen(std::sync::Arc::new(Name::NVar(mettail_runtime::OrdVar(
                mettail_runtime::Var::Free(mettail_runtime::get_or_create_var("a")),
            )))),
            Name::NQuote(std::sync::Arc::new(Proc::CastBytes(std::sync::Arc::new(
                Bytes::BytesLit(vec![]),
            )))),
        ],
        std::sync::Arc::new(Name::NQuoteNil),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "InputBindPolyadic(NQuoteNil, [NParen(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), NQuote(CastBytes(BytesLit([])))], NQuoteNil)";
    assert_eq!(
        canonicalize_debug(&format!("{:?}", term)),
        recorded,
        "the reconstructed term is not the recorded counterexample"
    );

    // 3 — the properties the corpus's generated suite checks for this category.
    let _ = format!("{:?}", term); // <cat>_debug_does_not_panic
    let _ = format!("{}", term); // <cat>_display_does_not_panic
    assert_eq!(term.clone(), term); // <cat>_clone_eq
}
