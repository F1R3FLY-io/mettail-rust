//! Corpus tests, per plan §7.
//!
//! Positive cases: the universal-algebra tower and the rho calculus built on
//! it. Negative cases: the two diagnostics carried over from the old
//! `bad/` directory, the new forward-reference diagnostic imposed by the
//! ordered builder chain, and the checks introduced by §3.4.

use mettail_elab::diag::DiagKind;
use mettail_elab::resolve::{MemResolver, ModuleRef, Resolver};
use mettail_elab::{elaborate, Presentation};

fn modules() -> MemResolver {
    MemResolver::new()
        .with("Rholang.module", include_str!("../examples/modules/Rholang.module"))
        .with("UnivAlg.module", include_str!("../examples/modules/UnivAlg.module"))
}

fn bad() -> MemResolver {
    MemResolver::new()
        .with("RepeatLabel.module", include_str!("../examples/modules/bad/RepeatLabel.module"))
        .with(
            "ReplacementShadows.module",
            include_str!("../examples/modules/bad/ReplacementShadows.module"),
        )
        .with(
            "ForwardReference.module",
            include_str!("../examples/modules/bad/ForwardReference.module"),
        )
        .with("ArgumentUse.module", include_str!("../examples/modules/bad/ArgumentUse.module"))
        .with(
            "UndeclaredCategory.module",
            include_str!("../examples/modules/bad/UndeclaredCategory.module"),
        )
        .with(
            "UnsharedName.module",
            include_str!("../examples/modules/bad/UnsharedName.module"),
        )
}

fn ok(file: &str, r: &dyn Resolver) -> Presentation {
    let reference = ModuleRef::parse(file).expect("valid test module reference");
    match elaborate(&reference, r) {
        Ok(p) => p,
        Err(d) => panic!("{file}: expected success, got {d}"),
    }
}

fn rejects(file: &str, kind: DiagKind, r: &dyn Resolver) {
    let reference = ModuleRef::parse(file).expect("valid test module reference");
    match elaborate(&reference, r) {
        Ok(_) => panic!("{file}: expected {:?}, but it elaborated", kind),
        Err(d) => assert_eq!(
            d.kind,
            kind,
            "{file}: expected {:?}, got {} ({})",
            kind,
            d.kind.name(),
            d.msg
        ),
    }
}

// ------------------------------------------------------------------ positive

#[test]
fn univalg_elaborates_to_a_ring() {
    let p = ok("UnivAlg.module", &modules());

    // One carrier, shared by both monoid structures: the pushout over
    // EmptySet (D3).
    assert_eq!(p.types.len(), 1, "a ring has one carrier");
    assert!(p.has_cat("Elem"));

    // Both structures survive, kept apart.
    for l in ["Zero", "Plus", "One", "Mult", "Neg"] {
        assert!(p.has_label(l), "missing `{l}`");
    }
    assert_eq!(p.terms.len(), 5);

    // Replacement carried the inherited equations with it: `Inv`'s laws are
    // now stated of `Neg`, `Mult` of `Plus`, `One` of `Zero`.
    let eqs = p.render();
    assert!(eqs.contains("(Plus x (Neg x)) == (Zero);"));
    assert!(!eqs.contains("(Inv"), "no `Inv` should survive the replacement");
}

#[test]
fn rholang_join_is_a_pushout() {
    let p = ok("Rholang.module", &modules());

    // The point of D3: NewReplCalc and RhoCalc both descend from one
    // QuoteDropCalc, so the join identifies what they share.
    assert_eq!(p.terms.iter().filter(|t| t.rule.label == "PPar").count(), 1, "exactly one PPar");
    for l in ["PDrop", "NQuote"] {
        assert_eq!(p.terms.iter().filter(|t| t.rule.label == l).count(), 1, "exactly one {l}");
    }
    assert_eq!(p.types.iter().filter(|c| c.cat == "Name").count(), 1, "exactly one Name");
    assert_eq!(p.types.len(), 2, "Proc and Name, nothing else");

    // Both halves are present.
    for l in ["PZero", "PPar", "PDrop", "NQuote", "PRepl", "PNew", "POutput", "PInput"] {
        assert!(p.has_label(l), "missing `{l}`");
    }
}

#[test]
fn rholang_carries_the_hard_forms() {
    let p = ok("Rholang.module", &modules());
    let r = p.render();

    // G2: collection sort and its rendering projection.
    assert!(r.contains("ps:HashBag(Proc)"));
    assert!(r.contains(r#"ps.*sep("|")"#));
    // G4: binder sort, abstraction, and two-argument substitution.
    assert!(r.contains("^x.p:[Name -> Proc]"));
    assert!(r.contains("(subst ^x.p (NQuote q))"));
    // G3: remainder patterns, on both sides of COMM.
    assert!(r.contains("...rest"));
    // Freshness side conditions survive elaboration.
    assert!(r.contains("if x # Q then"));
    // Conditional rewrites use the D2 spelling.
    assert!(r.contains("RPar : if S ~> T then"));
}

#[test]
fn parmonoid_renames_the_carrier_everywhere() {
    let p = ok("Rholang.module", &modules());
    assert!(p.has_cat("Proc"));
    assert!(!p.has_cat("Elem"), "`Elem` was renamed on export");
    let ppar = p.term("PPar").expect("PPar");
    assert_eq!(ppar.rule.result, "Proc");
}

#[test]
fn import_graph_is_recorded_for_reproducibility() {
    // Plan 9.1: a build records what it resolved. Content hashes replace the
    // sizes here once the surface carries them.
    let entry = ModuleRef::parse("Rholang.module").expect("valid module reference");
    let prog = mettail_elab::resolve::Program::load(&entry, &modules()).expect("load");
    let lock = prog.lockfile();
    assert_eq!(lock.len(), 2, "entry plus one import");
    assert!(lock
        .iter()
        .any(|(reference, _)| reference.external_form().ends_with("UnivAlg.module")));
}

// ------------------------------------------------------------------ negative

#[test]
fn rejects_repeat_label() {
    rejects("RepeatLabel.module", DiagKind::RepeatLabel, &bad());
}

#[test]
fn rejects_replacement_shadows() {
    rejects("ReplacementShadows.module", DiagKind::ReplacementShadows, &bad());
}

#[test]
fn rejects_forward_reference() {
    rejects("ForwardReference.module", DiagKind::ForwardReference, &bad());
}

#[test]
fn rejects_bad_argument_use() {
    rejects("ArgumentUse.module", DiagKind::ArgumentUse, &bad());
}

#[test]
fn rejects_undeclared_category() {
    rejects("UndeclaredCategory.module", DiagKind::UndeclaredCategory, &bad());
}

#[test]
fn rejects_join_of_independently_invented_categories() {
    rejects("UnsharedName.module", DiagKind::JoinCollision, &bad());
}

#[test]
fn diagnostics_are_located() {
    let reference = ModuleRef::parse("RepeatLabel.module").expect("valid module reference");
    let d = elaborate(&reference, &bad()).unwrap_err();
    assert!(d.span.line > 0, "a diagnostic must carry a source position");
    assert!(format!("{d}").contains("repeat-label"));
}

// ------------------------------------------------------------ surface detail

#[test]
fn implicit_empty_base() {
    // G5: a body opening with a builder needs no explicit `Empty`.
    let src = r#"
        Module G5 {
          Theory T() { Types { A; } Terms { X . |- "x" : A; } }
          theory T()
        }
    "#;
    let r = mettail_elab::resolve::MemResolver::new().with("m", src);
    let p = ok("m", &r);
    assert!(p.has_label("X"));
}

#[test]
fn canonical_data_builder_matches_dedicated_builders() {
    let dedicated = r#"
        Module Dedicated {
          Theory T() { Types { A; } Terms { X . |- "x" : A; } }
          theory T()
        }
    "#;
    let data = r#"
        Module DataForm {
          Theory T() {
            Data({
              "types": ["A"],
              "terms": [{
                "label": "X",
                "category": "A",
                "context": [],
                "syntax": [["lit", "x"]]
              }]
            })
          }
          theory T()
        }
    "#;
    let dedicated_resolver = MemResolver::new().with("dedicated", dedicated);
    let data_resolver = MemResolver::new().with("data", data);
    let dedicated = ok("dedicated", &dedicated_resolver);
    let data = ok("data", &data_resolver);
    assert_eq!(dedicated.render(), data.render());
}

#[test]
fn data_builder_rejects_whole_language_identity_keys() {
    let src = r#"
        Module BadData {
          Theory T() { Data({"name": "NotAFragment"}) }
          theory T()
        }
    "#;
    let resolver = MemResolver::new().with("bad-data", src);
    rejects("bad-data", DiagKind::Value, &resolver);
}

#[test]
fn unknown_collection_sort_is_named() {
    let src = r#"
        Module C {
          Theory T() { Types { A; } Terms { X . xs:Vector(A) |- "[" xs "]" : A; } }
          theory T()
        }
    "#;
    let r = mettail_elab::resolve::MemResolver::new().with("m", src);
    rejects("m", DiagKind::UnknownCollection, &r);
}

#[test]
fn separator_projection_requires_a_collection() {
    let src = r#"
        Module P {
          Theory T() { Types { A; } Terms { X . a:A |- "[" a.*sep(",") "]" : A; } }
          theory T()
        }
    "#;
    let r = mettail_elab::resolve::MemResolver::new().with("m", src);
    rejects("m", DiagKind::ArgumentUse, &r);
}

#[test]
fn meet_is_the_common_fragment() {
    // `Group /\ CommutativeMonoid` over a shared Monoid keeps the monoid.
    let src = r#"
        Module M {
          Theory Base() { Types { E; } Exports { E; } }
          Theory Mon(b: Base) { b Terms { One . |- "1" : E; } }
          Theory L(m: Mon) { m Terms { A . |- "a" : E; } }
          Theory R(m: Mon) { m Terms { B . |- "b" : E; } }
          Theory Common(l: L, r: R) { l /\ r }
          theory
            let b = Base() in (
            let m = Mon(b) in (
            Common(L(m), R(m))
            ))
        }
    "#;
    let r = mettail_elab::resolve::MemResolver::new().with("m", src);
    let p = ok("m", &r);
    assert!(p.has_label("One"), "the shared monoid survives the meet");
    assert!(!p.has_label("A"));
    assert!(!p.has_label("B"));
}

#[test]
fn difference_removes_by_origin() {
    let src = r#"
        Module D {
          Theory Base() { Types { E; } Exports { E; } }
          Theory Mon(b: Base) { b Terms { One . |- "1" : E; } }
          Theory Big(m: Mon) { m Terms { A . |- "a" : E; } }
          Theory Just(b: Big, m: Mon) { b \ m }
          theory
            let b = Base() in (
            let m = Mon(b) in (
            Just(Big(m), m)
            ))
        }
    "#;
    let r = mettail_elab::resolve::MemResolver::new().with("m", src);
    let p = ok("m", &r);
    assert!(p.has_label("A"));
    assert!(!p.has_label("One"), "inherited element removed by origin");
}

#[test]
fn import_cycles_are_reported() {
    let a = r#"import "b" as b  Module A { Theory T() { Types { X; } } theory T() }"#;
    let b = r#"import "a" as a  Module B { Theory U() { Types { Y; } } theory U() }"#;
    let r = mettail_elab::resolve::MemResolver::new()
        .with("a", a)
        .with("b", b);
    rejects("a", DiagKind::Resolution, &r);
}

#[test]
fn unreachable_import_is_reported() {
    let a = r#"import "nowhere" as n  Module A { Theory T() { Types { X; } } theory T() }"#;
    let r = mettail_elab::resolve::MemResolver::new().with("a", a);
    rejects("a", DiagKind::Resolution, &r);
}
