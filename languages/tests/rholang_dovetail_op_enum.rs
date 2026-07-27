//! Step B (Dovetail native-fold, Increment 2): the generated typed op-enum's exact-key
//! `SemanticHash`.
//!
//! `SemanticHash` is an `unsafe` trait whose contract is that two values produce identical
//! content bytes IFF they are `Eq`-equal. The generated `<Lang>DovetailOp` impl writes a
//! framed discriminant (cross-variant injectivity — two distinct variants never alias, even
//! with identical payloads) followed by the framed, `Eq`-agreeing payload bytes. A collision
//! would silently make the e-graph merge two distinct terms, so these properties are the
//! soundness floor of the typed fold path.
#![cfg(all(feature = "rholang", feature = "dovetail-codegen"))]

use dovetail::key::SemanticHash;
use mettail_languages::rholang::RholangDovetailOp as Op;

fn key(op: &Op) -> Vec<u8> {
    let mut out = Vec::new();
    op.write_content(&mut out);
    out
}

#[test]
fn framed_discriminant_prevents_cross_variant_aliasing() {
    // Two distinct payload-carrying variants with the SAME u32 payload must NOT alias: the
    // leading framed discriminant differs.
    assert_ne!(key(&Op::BinderArity(7)), key(&Op::FieldNone(7)));
    // A nullary/identity variant vs a payload-carrying variant.
    assert_ne!(key(&Op::Proc_Err), key(&Op::FieldNone(0)));
    // Distinct identity variants differ (discriminant only).
    assert_ne!(key(&Op::Proc_Err), key(&Op::Proc_PZero));
}

#[test]
fn numeric_payloads_distinct_and_deterministic() {
    assert_eq!(key(&Op::Int_NumLit(1)), key(&Op::Int_NumLit(1)), "deterministic");
    assert_ne!(key(&Op::Int_NumLit(1)), key(&Op::Int_NumLit(2)), "distinct payload");
    assert_ne!(key(&Op::Int_NumLit(-1)), key(&Op::Int_NumLit(1)), "sign matters");
}

#[test]
fn string_bool_and_opaque_payloads() {
    assert_ne!(key(&Op::Str_StringLit("a".into())), key(&Op::Str_StringLit("b".into())));
    assert_ne!(key(&Op::Bool_BoolLit(true)), key(&Op::Bool_BoolLit(false)));
    assert_ne!(key(&Op::FieldOpaque("a".into())), key(&Op::FieldOpaque("b".into())));
    assert_eq!(key(&Op::FieldOpaque("x".into())), key(&Op::FieldOpaque("x".into())));
}

#[test]
fn display_label_matches_string_path_projection() {
    // Display reproduces the String-path report-projection label form `Lang::Cat::Ctor`.
    assert_eq!(format!("{}", Op::Proc_Err), "Rholang::Proc::Err");
    assert_eq!(format!("{}", Op::Int_NumLit(3)), "Rholang::Int::NumLit(3)");
}
