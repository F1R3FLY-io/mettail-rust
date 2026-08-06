//! **Promoted counterexamples for `calculator`** — every seed its proptest corpus records,
//! as a named regression test.
//!
//! # Where these came from, and why they are here
//!
//! `languages/tests/gen_calculator_prop.proptest-regressions` holds 12 seed(s) for inputs
//! that ONCE FALSIFIED a property of this grammar, each with the shrunk counterexample
//! recorded beside it. proptest replays those seeds — but only while the corpus stays where
//! the language name puts it, and only as an anonymous seed nobody can name in a bug report.
//! A named `#[test]` per entry gives each counterexample an identity, a failure message and
//! a place in the ordinary test run.
//!
//! # How the term was recovered
//!
//! NOT by replaying the seed. proptest persists the seed of the case's FIRST generated
//! input and separately records the SHRUNK value's `Debug`, so replay reconstructs a
//! different, larger term (measured: `testkit/src/ctor.rs`). The `# shrinks to` text is the
//! only complete record, and `testkit`'s harvester reads it back through the constructor
//! schema the `rust_ctor` pass emits:
//!
//! ```text
//! cargo run -p testkit --bin harvest_proptest_corpus -- \
//!     target/generated/calculator/rust_ctor.rs \
//!     languages/tests/gen_calculator_prop.proptest-regressions
//! ```
//!
//! # The three assertions, and which one carries the weight
//!
//! 1. the term CONSTRUCTS;
//! 2. ★ its **normalised `Debug` equals the corpus-recorded text**, carried here as a
//!    literal. This is the anti-vacuity core: a test that merely constructed *some* term
//!    would pass while proving nothing, and this assertion makes that impossible. Only
//!    `UniqueId(n)` is normalised — it is drawn from a process-global counter and is not a
//!    property of the term (`FreeVar` equality is by `unique_id` alone, and the generated
//!    strategies mint every variable through the thread-local name cache, so the NAME fixes
//!    the identity);
//! 3. the properties the generated suite checks for this category.
//!
//! # RED proof
//!
//! Mutate one constructor in any test below — swap `PZero` for a sibling, perturb an
//! integer — and assertion 2 goes RED, while every other test in the file still passes. The
//! unmutated terms' `Debug` matches its recorded text exactly, which is the control.

#![allow(clippy::needless_borrow)]

use mettail_languages::calculator::*;
use mettail_testkit::ctor::canonicalize_debug;

/// Corpus entry 0 — seed `cc 9b64dcbd8882433a0ed91bfa0064515dbab73a168a4e3699be9bfec9a06f62ad`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = GtStr(Concat(Concat(StringLit("ae"), StringLit("aaa")), Concat(StringLit("a"),
/// StringLit("aaaaaaa"))), AddStr(AddStr(StringLit("bxwa"), StringLit("haaa")),
/// Concat(StringLit("a"), StringLit("aaaaaaa"))))
/// ```
#[test]
fn corpus_0_bool() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Bool = Bool::GtStr(
        std::sync::Arc::new(Str::Concat(
            std::sync::Arc::new(Str::Concat(
                std::sync::Arc::new(Str::StringLit(std::string::String::from("ae"))),
                std::sync::Arc::new(Str::StringLit(std::string::String::from("aaa"))),
            )),
            std::sync::Arc::new(Str::Concat(
                std::sync::Arc::new(Str::StringLit(std::string::String::from("a"))),
                std::sync::Arc::new(Str::StringLit(std::string::String::from("aaaaaaa"))),
            )),
        )),
        std::sync::Arc::new(Str::AddStr(
            std::sync::Arc::new(Str::AddStr(
                std::sync::Arc::new(Str::StringLit(std::string::String::from("bxwa"))),
                std::sync::Arc::new(Str::StringLit(std::string::String::from("haaa"))),
            )),
            std::sync::Arc::new(Str::Concat(
                std::sync::Arc::new(Str::StringLit(std::string::String::from("a"))),
                std::sync::Arc::new(Str::StringLit(std::string::String::from("aaaaaaa"))),
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
    let recorded = "GtStr(Concat(Concat(StringLit(\"ae\"), StringLit(\"aaa\")), Concat(StringLit(\"a\"), StringLit(\"aaaaaaa\"))), AddStr(AddStr(StringLit(\"bxwa\"), StringLit(\"haaa\")), Concat(StringLit(\"a\"), StringLit(\"aaaaaaa\"))))";
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

/// Corpus entry 1 — seed `cc 966b86e06085e4b9871d7c7c370cd6558e397d920d6caddf45dd43a44768b553`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = BoolToUInt32(EqInt(Tern(Err, NumLit(475223836), Err), DivInt(CastErrInt, Err)))
/// ```
#[test]
fn corpus_1_uint32() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: UInt32 = UInt32::BoolToUInt32(std::sync::Arc::new(Bool::EqInt(
        std::sync::Arc::new(Int::Tern(
            std::sync::Arc::new(Int::Err),
            std::sync::Arc::new(Int::NumLit(475223836i32)),
            std::sync::Arc::new(Int::Err),
        )),
        std::sync::Arc::new(Int::DivInt(
            std::sync::Arc::new(Int::CastErrInt),
            std::sync::Arc::new(Int::Err),
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
    let recorded =
        "BoolToUInt32(EqInt(Tern(Err, NumLit(475223836), Err), DivInt(CastErrInt, Err)))";
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

/// Corpus entry 2 — seed `cc 9c8a9bf9fa8b23af0717837cba86ce72746fea27f12873b86b7644ebbe21664c`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = BoolToInt(LtEqInt(Neg(Err), Fact(Err)))
/// ```
#[test]
fn corpus_2_int() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Int = Int::BoolToInt(std::sync::Arc::new(Bool::LtEqInt(
        std::sync::Arc::new(Int::Neg(std::sync::Arc::new(Int::Err))),
        std::sync::Arc::new(Int::Fact(std::sync::Arc::new(Int::Err))),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "BoolToInt(LtEqInt(Neg(Err), Fact(Err)))";
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

/// Corpus entry 3 — seed `cc 6655eef3551c5d63a23e028e7786f9814a641349250fb0cac8bdffc9bf82ed75`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = NeInt(LenList(KeysMap(MapLit(HashMapLit({})))), BoolToInt(And(BoolLit(false),
/// BoolLit(true))))
/// ```
#[test]
fn corpus_3_bool() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Bool = Bool::NeInt(
        std::sync::Arc::new(Int::LenList(std::sync::Arc::new(List::KeysMap(std::sync::Arc::new(
            Map::MapLit(mettail_runtime::HashMapLit::from_iter(vec![])),
        ))))),
        std::sync::Arc::new(Int::BoolToInt(std::sync::Arc::new(Bool::And(
            std::sync::Arc::new(Bool::BoolLit(false)),
            std::sync::Arc::new(Bool::BoolLit(true)),
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
    let recorded = "NeInt(LenList(KeysMap(MapLit(HashMapLit({})))), BoolToInt(And(BoolLit(false), BoolLit(true))))";
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

/// Corpus entry 4 — seed `cc b79988dabdf309ac950bcdffa27e9e80ae2c944793474490336c991ed96879ce`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = GtEqInt(Tern(AddInt(NumLit(0), Err), BitNotInt(Err), FloatToInt(CastErrFloat)), Err)
/// ```
#[test]
fn corpus_4_bool() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Bool = Bool::GtEqInt(
        std::sync::Arc::new(Int::Tern(
            std::sync::Arc::new(Int::AddInt(
                std::sync::Arc::new(Int::NumLit(0i32)),
                std::sync::Arc::new(Int::Err),
            )),
            std::sync::Arc::new(Int::BitNotInt(std::sync::Arc::new(Int::Err))),
            std::sync::Arc::new(Int::FloatToInt(std::sync::Arc::new(Float::CastErrFloat))),
        )),
        std::sync::Arc::new(Int::Err),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded =
        "GtEqInt(Tern(AddInt(NumLit(0), Err), BitNotInt(Err), FloatToInt(CastErrFloat)), Err)";
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

/// Corpus entry 5 — seed `cc 33ee3dd75713058d83ee16522cf93b909a4614e3276201c176114023dd7ce517`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = AddFixed(AddFixed(NegFixed(CastErrFixed), BitNotFixed(FixedLit(Fixed(0/1)))),
/// FixedBin(ProcUInt32(CastErrUInt32), Err))
/// ```
#[test]
fn corpus_5_fixed() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Fixed = Fixed::AddFixed(
        std::sync::Arc::new(Fixed::AddFixed(
            std::sync::Arc::new(Fixed::NegFixed(std::sync::Arc::new(Fixed::CastErrFixed))),
            std::sync::Arc::new(Fixed::BitNotFixed(std::sync::Arc::new(Fixed::FixedLit(
                mettail_runtime::CanonicalFixedPoint::new(num_bigint::BigInt::from(0i64), 0u32),
            )))),
        )),
        std::sync::Arc::new(Fixed::FixedBin(
            std::sync::Arc::new(Proc::ProcUInt32(std::sync::Arc::new(UInt32::CastErrUInt32))),
            std::sync::Arc::new(Int::Err),
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
    let recorded = "AddFixed(AddFixed(NegFixed(CastErrFixed), BitNotFixed(FixedLit(Fixed(0/1)))), FixedBin(ProcUInt32(CastErrUInt32), Err))";
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

/// Corpus entry 6 — seed `cc c1685875c8662d63ef3f8085a30ea87ad80221f82e62397face71cd1dc57b911`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = ProcBigRat(BitAndBigRat(BitAndBigRat(RatLit(Ratio { numer: 0, denom: 1 }),
/// RatLit(Ratio { numer: 0, denom: 1 })), BigratCast(PVar(OrdVar(Free(FreeVar { unique_id:
/// UniqueId(51), pretty_name: Some("a") }))))))
/// ```
#[test]
fn corpus_6_proc() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Proc = Proc::ProcBigRat(std::sync::Arc::new(BigRat::BitAndBigRat(
        std::sync::Arc::new(BigRat::BitAndBigRat(
            std::sync::Arc::new(BigRat::RatLit(mettail_runtime::CanonicalBigRat::from(
                num_rational::BigRational::new(
                    num_bigint::BigInt::from(0i64),
                    num_bigint::BigInt::from(1i64),
                ),
            ))),
            std::sync::Arc::new(BigRat::RatLit(mettail_runtime::CanonicalBigRat::from(
                num_rational::BigRational::new(
                    num_bigint::BigInt::from(0i64),
                    num_bigint::BigInt::from(1i64),
                ),
            ))),
        )),
        std::sync::Arc::new(BigRat::BigratCast(std::sync::Arc::new(Proc::PVar(
            mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )),
        )))),
    )));

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "ProcBigRat(BitAndBigRat(BitAndBigRat(RatLit(Ratio { numer: 0, denom: 1 }), RatLit(Ratio { numer: 0, denom: 1 })), BigratCast(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))))";
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

/// Corpus entry 7 — seed `cc 28ad1a5a21dbac4caef32ff93a83ac62b056e86dec92f1be7c62815c7bbf8271`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = AddBigRat(RatLit(Ratio { numer: 0, denom: 1 }), BigratCast(PVar(OrdVar(Free(FreeVar {
/// unique_id: UniqueId(0), pretty_name: Some("a") })))))
/// ```
#[test]
fn corpus_7_bigrat() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: BigRat = BigRat::AddBigRat(
        std::sync::Arc::new(BigRat::RatLit(mettail_runtime::CanonicalBigRat::from(
            num_rational::BigRational::new(
                num_bigint::BigInt::from(0i64),
                num_bigint::BigInt::from(1i64),
            ),
        ))),
        std::sync::Arc::new(BigRat::BigratCast(std::sync::Arc::new(Proc::PVar(
            mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("a"),
            )),
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
    let recorded = "AddBigRat(RatLit(Ratio { numer: 0, denom: 1 }), BigratCast(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))))";
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

/// Corpus entry 8 — seed `cc 0be7f6367e06ccf4d41dc047cc18c6e76df9ff14ab821698f48de068525ee5d1`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = GtEqBool(GtEqBool(GtEqBool(BoolLit(true), BoolLit(true)), GtEqBool(BoolLit(true),
/// BoolLit(true))), GtEqBool(GtEqBool(BoolLit(true), BoolLit(true)), GtEqBool(BoolLit(true),
/// BoolLit(true))))
/// ```
#[test]
fn corpus_8_bool() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Bool = Bool::GtEqBool(
        std::sync::Arc::new(Bool::GtEqBool(
            std::sync::Arc::new(Bool::GtEqBool(
                std::sync::Arc::new(Bool::BoolLit(true)),
                std::sync::Arc::new(Bool::BoolLit(true)),
            )),
            std::sync::Arc::new(Bool::GtEqBool(
                std::sync::Arc::new(Bool::BoolLit(true)),
                std::sync::Arc::new(Bool::BoolLit(true)),
            )),
        )),
        std::sync::Arc::new(Bool::GtEqBool(
            std::sync::Arc::new(Bool::GtEqBool(
                std::sync::Arc::new(Bool::BoolLit(true)),
                std::sync::Arc::new(Bool::BoolLit(true)),
            )),
            std::sync::Arc::new(Bool::GtEqBool(
                std::sync::Arc::new(Bool::BoolLit(true)),
                std::sync::Arc::new(Bool::BoolLit(true)),
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
    let recorded = "GtEqBool(GtEqBool(GtEqBool(BoolLit(true), BoolLit(true)), GtEqBool(BoolLit(true), BoolLit(true))), GtEqBool(GtEqBool(BoolLit(true), BoolLit(true)), GtEqBool(BoolLit(true), BoolLit(true))))";
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

/// Corpus entry 9 — seed `cc cdf91c397202ae497ef6dec68764b3eec85f9603fd0ba3980cf5b7a0d9a5ee64`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = BoolToFloat(EqFixed(AddFixed(FixedLit(Fixed(0/1)), FixedLit(Fixed(-2147483648/1))),
/// SubFixed(CastErrFixed, CastErrFixed)))
/// ```
#[test]
fn corpus_9_float() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: Float = Float::BoolToFloat(std::sync::Arc::new(Bool::EqFixed(
        std::sync::Arc::new(Fixed::AddFixed(
            std::sync::Arc::new(Fixed::FixedLit(mettail_runtime::CanonicalFixedPoint::new(
                num_bigint::BigInt::from(0i64),
                0u32,
            ))),
            std::sync::Arc::new(Fixed::FixedLit(mettail_runtime::CanonicalFixedPoint::new(
                num_bigint::BigInt::from(-2147483648i64),
                0u32,
            ))),
        )),
        std::sync::Arc::new(Fixed::SubFixed(
            std::sync::Arc::new(Fixed::CastErrFixed),
            std::sync::Arc::new(Fixed::CastErrFixed),
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
    let recorded = "BoolToFloat(EqFixed(AddFixed(FixedLit(Fixed(0/1)), FixedLit(Fixed(-2147483648/1))), SubFixed(CastErrFixed, CastErrFixed)))";
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

/// Corpus entry 10 — seed `cc b35c625b1da7b4dfcdddbfc5a8c36d4c034e57a0544764b58cf4ccdeb0a799fe`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = MulBigRat(AddBigRat(RatLit(Ratio { numer: 0, denom: 1 }),
/// BigratCast(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(37), pretty_name: Some("a")
/// }))))), Err)
/// ```
#[test]
fn corpus_10_bigrat() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: BigRat = BigRat::MulBigRat(
        std::sync::Arc::new(BigRat::AddBigRat(
            std::sync::Arc::new(BigRat::RatLit(mettail_runtime::CanonicalBigRat::from(
                num_rational::BigRational::new(
                    num_bigint::BigInt::from(0i64),
                    num_bigint::BigInt::from(1i64),
                ),
            ))),
            std::sync::Arc::new(BigRat::BigratCast(std::sync::Arc::new(Proc::PVar(
                mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                    mettail_runtime::get_or_create_var("a"),
                )),
            )))),
        )),
        std::sync::Arc::new(BigRat::Err),
    );

    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the
    //     text the corpus recorded, character for character. This is what makes
    //     "passes because it built the wrong term" impossible. Only
    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented
    //     out, and both are properties of the PROCESS rather than of the term:
    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by
    //     unique_id alone, with the name fixing the identity through the var
    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.
    let recorded = "MulBigRat(AddBigRat(RatLit(Ratio { numer: 0, denom: 1 }), BigratCast(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))))), Err)";
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

/// Corpus entry 11 — seed `cc 9a9da5768e9356ec09d7fdf86fd3f8f3d36508ed1aa4b45b849f154091a82825`.
///
/// Recorded counterexample, verbatim from the corpus:
/// ```text
/// term = MulBigRat(MulBigRat(AddBigRat(RatLit(Ratio { numer: 0, denom: 1 }), RatLit(Ratio {
/// numer: 0, denom: 1 })), RatLit(Ratio { numer: 0, denom: 1 })),
/// BitAndBigRat(FixedToBigRat(FixedLit(Fixed(0/1))), FixedToBigRat(FixedLit(Fixed(0/1)))))
/// ```
#[test]
fn corpus_11_bigrat() {
    mettail_runtime::clear_var_cache();
    // 1 — the term CONSTRUCTS.
    let term: BigRat = BigRat::MulBigRat(
        std::sync::Arc::new(BigRat::MulBigRat(
            std::sync::Arc::new(BigRat::AddBigRat(
                std::sync::Arc::new(BigRat::RatLit(mettail_runtime::CanonicalBigRat::from(
                    num_rational::BigRational::new(
                        num_bigint::BigInt::from(0i64),
                        num_bigint::BigInt::from(1i64),
                    ),
                ))),
                std::sync::Arc::new(BigRat::RatLit(mettail_runtime::CanonicalBigRat::from(
                    num_rational::BigRational::new(
                        num_bigint::BigInt::from(0i64),
                        num_bigint::BigInt::from(1i64),
                    ),
                ))),
            )),
            std::sync::Arc::new(BigRat::RatLit(mettail_runtime::CanonicalBigRat::from(
                num_rational::BigRational::new(
                    num_bigint::BigInt::from(0i64),
                    num_bigint::BigInt::from(1i64),
                ),
            ))),
        )),
        std::sync::Arc::new(BigRat::BitAndBigRat(
            std::sync::Arc::new(BigRat::FixedToBigRat(std::sync::Arc::new(Fixed::FixedLit(
                mettail_runtime::CanonicalFixedPoint::new(num_bigint::BigInt::from(0i64), 0u32),
            )))),
            std::sync::Arc::new(BigRat::FixedToBigRat(std::sync::Arc::new(Fixed::FixedLit(
                mettail_runtime::CanonicalFixedPoint::new(num_bigint::BigInt::from(0i64), 0u32),
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
    let recorded = "MulBigRat(MulBigRat(AddBigRat(RatLit(Ratio { numer: 0, denom: 1 }), RatLit(Ratio { numer: 0, denom: 1 })), RatLit(Ratio { numer: 0, denom: 1 })), BitAndBigRat(FixedToBigRat(FixedLit(Fixed(0/1))), FixedToBigRat(FixedLit(Fixed(0/1)))))";
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
