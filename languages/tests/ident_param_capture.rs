//! `m:Ident` — the builtin-`Ident` mid-rule param, end-to-end.
//!
//! This TEST fixture (it lives in `languages/tests/`, never `languages/src/`) proves the
//! `NonTerminalKind::Ident` pipeline on a language small enough to compile in seconds, so
//! the seams are verified BEFORE the ~25-minute Rholang cycle depends on them: a param
//! declared `m:Ident` consumes ONE builtin `Token::Ident`, its text lands in the AST as a
//! bare `String`, it is bound in the native `![...]` action, rendered by `Display`
//! (round-trip), and carried inertly through the term operations.
//!
//! # Why this is not a duplicate of `l9_modal_toy.rs`
//!
//! `l9_modal_toy` proves the L9-3 path: a DECLARED `tokens { }` kind consumed by a
//! `w@Word` capture. This proves the disjoint path: the BUILTIN `Ident` kind consumed by
//! an ordinary term-context param. The two differ in every seam that matters —
//! `SyntaxExpr::TokenKind` vs `SyntaxExpr::Param`, `TokenKindCapture` vs
//! `IdentTextCapture`, `GuardedConsumeTokenKindAndReplace` vs `ConsumeIdentAndReplace`,
//! `as_token_text()` vs `as_ident()`, and `capture_layout(..) == Some` vs `None` — so
//! neither fixture can fail for the other's reason.
//!
//! # ★ The measurement that made this path necessary
//!
//! Reaching a mid-rule `String` through a DECLARED kind co-extensive with `Ident` was
//! measured on Rholang and rejected: multi-accept DFA states 4/474 (0.8 %) → 379/475
//! (79.8 %), alt-accept edges 482 → 1234 (×2.56), parse time geomean ×2.49 / worst ×8.59
//! over the shipped corpus, with identifier-free inputs flat at ×1.03 as the control.
//! `NonTerminalKind::Ident` consumes the token class that already exists, so it adds no
//! co-accept at all.
//!
//! # ★ The discrimination this fixture exists to make: `Ident` is NOT `Var`
//!
//! Both surfaces consume one identifier token. They differ in the CARRIER: `m:Var` yields
//! `mettail_runtime::OrdVar`, which the term operations treat as a variable — `subst`
//! canonicalises `Var::Free` under unify, so a binder in scope can capture it. `m:Ident`
//! yields `String`, which no term operation can see into. `named_field_is_a_string_not_a_var`
//! makes that a COMPILE-TIME fact rather than a runtime hope.

#![allow(unused_imports, dead_code)]

use mettail_runtime::Language;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use mettail_macros::language;

language! {
    name: IdentParamToy,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        // ⚠ NOT native-typed (`![i32] as Num`). A native-typed category makes the macro
        // emit a stack-safe `try_eval` frame for EVERY rule, and that frame's classifier
        // (`classify_hol_rule_for_pda`) rejects any `TypeExpr::Collection` param — so a
        // native `Num` plus a `Vec` param fails for a PRE-EXISTING reason unrelated to
        // `Ident`. Rholang's `Proc` is likewise not native-typed, which is why its own
        // `Vec`-param rules (`POutput2Plus`, …) compile today. Matching that here keeps
        // the fixture's failures attributable to the mechanism under test.
        Num
    },

    terms {
        Lit . |- "#" : Num ;

        // THE shape under test, and it is deliberately the shape Rholang's collapsed
        // method rule needs: a leading category param, a mid-rule `Ident` param, and a
        // trailing `Vec` collection between delimiters. `capture_layout` returns `None`
        // here (no `SyntaxExpr::TokenKind`), so all three fields come from the ordinary
        // term-context path — which is exactly why this shape works where a `m@Kind`
        // capture cannot: `macros/src/gen/capture.rs:202-208` drops `Sep`/`Zip`/`Map`
        // meta-ops on the floor, so a capture next to a collection would silently lose
        // the collection field.
        //
        // ⚠ `fold`, not a bare native-eval action — matching how Rholang writes EVERY
        // `Vec`-param rule (`POutput2Plus`, `PPersistOutput2Plus`, …). A bare `![...]` on
        // a native-typed category routes through `classify_hol_rule_for_pda`
        // (`macros/src/gen/native/eval.rs:88`), whose `collect` returns `None` for any
        // `TypeExpr::Collection` param — so a `Vec` param plus native eval is a
        // PRE-EXISTING macro limitation, unrelated to `Ident`, and asserting against it
        // here would make this fixture fail for a reason it is not testing.
        // An IDENTITY fold (the shape `NParen` uses in Rholang): it reconstructs itself,
        // so normalization is a no-op and `parse ∘ display` stays observable. What it
        // proves is that the three field types the collapse needs — `Arc<Num>`, `String`,
        // `Vec<Num>` — are what the macro actually emits, in that order: the body would
        // not type-check against any other layout.
        Call . recv:Num, m:Ident, args:Vec(Num)
        |- recv "." m "(" args.*sep(",") ")" : Num ![{
            Num::Call(std::sync::Arc::new(recv.clone()), m.clone(), args.clone())
        }] fold;

        // A bare mid-rule `Ident` with no collection — the minimal form, so a failure in
        // `Call` can be localised to the collection interaction rather than the capture.
        // ⚠ MEASURED LIMITATION, RECORDED HERE SO IT IS NOT REDISCOVERED: this fold is
        // DECLINED by the lowering gate, and the declination is correct. A fold body is
        // lowered against the Dovetail DERIVATION, binding each param through that
        // category's `__mettail_dovetail_build_<cat>_d` reconstructor; an `Ident` field
        // has none, and cannot be given one, because an opaque-leaf capture lowers to a
        // LOSSY e-graph leaf from which the identifier's text is not recoverable.
        //
        // So the rule stands as a PARSE/DISPLAY fixture, and the assertions below claim
        // only what is true: the text is captured into a `String` field, survives
        // `parse ∘ display`, and participates in `Eq`/`Hash`. Any design that needs a
        // fold to DISPATCH on a captured name must first make the opaque leaf invertible
        // for `TokenText` — a derivation-lowering change, not a codegen tweak.
        Tagged . m:Ident |- "tag" m : Num ![{
            match m.as_str() {
                "zero" => Num::Lit,
                _ => Num::Tagged(m.clone()),
            }
        }] fold;

        // ★ THE SECOND DRIVER ARM. `Call`'s capture is part 0, so it is reached through
        // the PRE-operand literal run (`kind: 2`). A capture that FOLLOWS another operand
        // is reached through the BETWEEN-operand run (`kind: 1`) instead — a structurally
        // different arm which must additionally BUMP the mixfix marker to the capture's
        // part index, because for a capture there is no sub-parse whose return would
        // otherwise bump it.
        //
        // ⚠ THIS RULE EXISTS BECAUSE THE ARM WOULD OTHERWISE SHIP UNEXERCISED. Nothing on
        // `Call`'s path enters it, so the whole fixture could be green with that arm
        // wrong — the precise shape of false zero this campaign has recorded repeatedly
        // ("a symbol exists, therefore the path works"). Here the parts are `b` (an
        // ordinary operand, following `:`) and then `m` (the capture, no following), so
        // the parse cannot succeed unless the `kind: 1` hand-off is correct.
        Pick . a:Num, b:Num, m:Ident
        |- a "?" b ":" m : Num ![{
            Num::Pick(
                std::sync::Arc::new(a.clone()),
                std::sync::Arc::new(b.clone()),
                m.clone(),
            )
        }] fold;
    },
}

#[test]
fn ident_param_language_resolves() {
    let lang = IdentParamToyLanguage;
    assert_eq!(lang.name(), "IdentParamToy");
}

/// ★ THE DISCRIMINATOR, and it is enforced by the COMPILER.
///
/// `Num::Tagged(String)` type-checks only if the `m:Ident` param lowered to
/// `std::string::String`. Had it lowered to `mettail_runtime::OrdVar` — which is what
/// `m:Var` produces (`macros/src/gen/types/enums.rs:635`) — this file would not build.
/// A runtime assertion could not make this distinction as sharply: `OrdVar` also carries
/// a name, so a value-level check could pass against the wrong carrier.
#[test]
fn named_field_is_a_string_not_a_var() {
    let t: Num = Num::Tagged("nth".to_string());
    assert_eq!(t, Num::Tagged("nth".to_string()));
}

#[test]
fn bare_ident_param_parses_into_a_string_field() {
    mettail_runtime::clear_var_cache();
    let term = Num::parse("tag abc").expect("mid-rule `m:Ident` parse");
    assert_eq!(term, Num::Tagged("abc".to_string()));
}

/// The name is DATA, not identity: two calls that differ only in the identifier must be
/// distinct under every term operation. Without this, a collapsed method surface could
/// conflate `l.nth(0)` with `l.last(0)` and no other test in this file would notice.
#[test]
fn distinct_names_are_distinct_terms_under_eq_hash_ord() {
    mettail_runtime::clear_var_cache();
    let foo = Num::parse("# . foo ( )").expect("parse foo");
    let bar = Num::parse("# . bar ( )").expect("parse bar");
    assert_ne!(foo, bar, "terms differing only in the Ident field must not be equal");

    let h = |t: &Num| {
        let mut s = DefaultHasher::new();
        t.hash(&mut s);
        s.finish()
    };
    assert_ne!(h(&foo), h(&bar), "distinct names must hash apart");
    assert_ne!(
        foo.cmp(&bar),
        std::cmp::Ordering::Equal,
        "distinct names must order apart"
    );
}

/// ★ The shape Rholang's collapse depends on: `Ident` param IMMEDIATELY followed by a
/// `Vec` collection, at every arity the method surface uses (measured: 20 nullary, 22
/// unary, 2 binary — max 2).
#[test]
fn ident_param_beside_a_vec_collection_parses_at_every_arity() {
    mettail_runtime::clear_var_cache();
    for (src, argc) in [("# . f ( )", 0usize), ("# . f ( # )", 1), ("# . f ( # , # )", 2)] {
        let term = Num::parse(src).unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"));
        match &term {
            Num::Call(_, m, args) => {
                assert_eq!(m, "f", "the Ident field must carry the method name");
                assert_eq!(args.len(), argc, "`{src}` must carry {argc} argument(s)");
            },
            other => panic!("`{src}` must parse as Call, got {other:?}"),
        }
    }
}

/// ★ THE `kind: 1` DRIVER ARM — a capture that is NOT the first part.
///
/// `Pick`'s parts are `b` (an ordinary operand) and then `m` (the capture), so reaching
/// `m` requires the BETWEEN-operand hand-off: consume one `Ident` AND bump the mixfix
/// marker to part 1. `Call` never enters that arm, so without this test the arm would
/// ship unexercised and the suite would still be green — the exact false zero this
/// campaign keeps recording.
///
/// The assertions discriminate: `m` must carry the NAME (not the empty string a silent
/// default would leave), and both operands must be present in order.
#[test]
fn a_capture_after_another_operand_parses_through_the_between_operand_arm() {
    mettail_runtime::clear_var_cache();
    let term = Num::parse("# ? # : g").expect("`# ? # : g` must parse");
    match &term {
        Num::Pick(a, b, m) => {
            assert_eq!(m, "g", "the Ident field must carry the captured name");
            assert_eq!(**a, Num::Lit, "the first operand is the leading `#`");
            assert_eq!(**b, Num::Lit, "the second operand is the inner `#`");
        },
        other => panic!("`# ? # : g` must parse as Pick, got {other:?}"),
    }
    // The name is DATA here too: two picks differing only in the identifier stay distinct.
    let other = Num::parse("# ? # : h").expect("`# ? # : h` must parse");
    assert_ne!(term, other, "picks differing only in the Ident field must not be equal");
}

/// `parse ∘ display` is stable — the named gate for any new field kind. A `String` field
/// that rendered quoted (the way a `StringLiteral` param does) would fail here, which is
/// the specific regression this catches.
#[test]
fn ident_param_display_round_trips() {
    mettail_runtime::clear_var_cache();
    for src in ["tag abc", "# . f ( )", "# . f ( # , # )", "# ? # : g"] {
        let term = Num::parse(src).expect("parse");
        let printed = format!("{}", term);
        let reparsed = Num::parse(&printed)
            .unwrap_or_else(|e| panic!("re-parse of display {printed:?} failed: {e:?}"));
        assert_eq!(reparsed, term, "round-trip failed for {src:?} (printed {printed:?})");
    }
}
