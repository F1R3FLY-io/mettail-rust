//! Agreement snapshot for the OSLF substrate Phase 4 `.0`-inert symbolic
//! tree-transducer cast analysis (`sym_tree_transducer::analyze_from_bundle`).
//!
//! For each cast / refinement rule `r : src → tgt`, the cast transducer's
//! **pre-image** ([`SymbolicTreeTransducer::domain_sta`], exposed as
//! `sym_tree_transducer::cast_preimage_automaton`) must accept **exactly** the
//! source category's terms — i.e. it must be language-equivalent, category-for-
//! category, to the Phase-2 `structural_types::category_automaton` of `src`.
//! That is the `.0`-inert contract and the agreement gate that authorizes the
//! `.1` supersede: the transducer merely *generalizes* the source-category
//! recognizer to a transduction; over the cast's domain it must not change which
//! source terms are recognized.
//!
//! ## What is compared
//!
//! Both automata are built over the **identical** Phase-2 ranked alphabet
//! (`structural_types::ranked_alphabet` / `build_tree_algebra`). Language
//! equivalence is decided by an **empty symmetric difference** over that shared
//! alphabet:
//!
//!   `L(preimage) = L(category)`  ⟺  `(preimage ∩ ¬category)` is empty
//!                                AND `(category ∩ ¬preimage)` is empty
//!
//! (the `is_equivalent` reduction, available via `intersect` / `complement` /
//! `is_empty` on `SymbolicTreeAutomaton`). On any disagreement the offending cast
//! is named and the test FAILS — a genuine disagreement is a real finding, never
//! papered over.
//!
//! The fixture mirrors the refinement-cast corpus grammars (refinementsmoke's
//! `Int`-refinements `PosInt` / `NegInt`, plus calculator-style numeric casts
//! into `Proc`), constructed with the same `RefinementTypeSpec` /
//! `term`/`nonterm`/`rule` helpers the sibling `.0` and refinement pipeline tests
//! (`prattail/src/pipeline/tests.rs`, `sym_tree_structural_snapshot.rs`) use.

#![cfg(feature = "oslf-transducer")]

use mettail_prattail::any_algebra::AnyAlgebra;
use mettail_prattail::pipeline::CategoryInfo;
use mettail_prattail::structural_types::{build_tree_algebra, category_automaton, ranked_alphabet};
use mettail_prattail::sym_tree::SymbolicTreeAutomaton;
use mettail_prattail::sym_tree_transducer::{analyze_from_bundle, cast_preimage_automaton};
use mettail_prattail::{RefinementPredKind, RefinementTypeSpec, SyntaxItemSpec};

// ── Tiny constructors for readable fixtures ─────────────────────────────────

type SyntaxRule = (String, String, Vec<SyntaxItemSpec>);

fn term(s: &str) -> SyntaxItemSpec {
    SyntaxItemSpec::Terminal(s.to_string())
}
fn nonterm(cat: &str, name: &str) -> SyntaxItemSpec {
    SyntaxItemSpec::NonTerminal {
        category: cat.to_string(),
        param_name: name.to_string(),
    }
}
fn ident(name: &str) -> SyntaxItemSpec {
    SyntaxItemSpec::IdentCapture { param_name: name.to_string() }
}
fn scalar_cat(name: &str, native: &str) -> CategoryInfo {
    CategoryInfo {
        name: name.to_string(),
        native_type: Some(native.to_string()),
        is_primary: false,
        has_var: true,
    }
}
fn struct_cat(name: &str, is_primary: bool, has_var: bool) -> CategoryInfo {
    CategoryInfo {
        name: name.to_string(),
        native_type: None,
        is_primary,
        has_var,
    }
}
fn rule(label: &str, cat: &str, syntax: Vec<SyntaxItemSpec>) -> SyntaxRule {
    (label.to_string(), cat.to_string(), syntax)
}
fn refinement(name: &str, base: &str) -> RefinementTypeSpec {
    RefinementTypeSpec {
        name: name.to_string(),
        base_category: base.to_string(),
        variable_name: "x".to_string(),
        predicate_kind: RefinementPredKind::Presburger,
        predicate_repr: "x > 0".to_string(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Language-equivalence helper (empty symmetric difference over the shared
// ranked alphabet — the `is_equivalent` reduction).
// ══════════════════════════════════════════════════════════════════════════════

fn languages_equal(
    a: &SymbolicTreeAutomaton<AnyAlgebra>,
    b: &SymbolicTreeAutomaton<AnyAlgebra>,
) -> bool {
    // a \ b = a ∩ ¬b ; b \ a = b ∩ ¬a. Both empty ⟺ L(a) = L(b).
    let a_minus_b = a.intersect(&b.complement());
    if !a_minus_b.is_empty() {
        return false;
    }
    let b_minus_a = b.intersect(&a.complement());
    b_minus_a.is_empty()
}

// ══════════════════════════════════════════════════════════════════════════════
// Fixture: refinement casts + numeric casts
// ══════════════════════════════════════════════════════════════════════════════

/// A grammar with:
///   - `Int` scalar (with a variable rule `IVar` and a literal `IZero` so it is
///     inhabited),
///   - refinement categories `PosInt` / `NegInt` over `Int` with downcast rules
///     `IntToPos : PosInt ::= Int` and `IntToNeg : NegInt ::= Int`,
///   - a `Proc` super-category with numeric casts `ProcInt : Proc ::= Int` and
///     `ProcPos : Proc ::= PosInt` (a cast whose source is itself a refinement
///     category).
///
/// Returns `(all_syntax, categories, refinement_types)`.
fn refinement_cast_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>, Vec<RefinementTypeSpec>) {
    let categories = vec![
        struct_cat("Proc", true, true),
        scalar_cat("Int", "i64"),
        struct_cat("PosInt", false, true),
        struct_cat("NegInt", false, true),
    ];
    let all_syntax = vec![
        rule("IVar", "Int", vec![ident("x")]),
        rule("IZero", "Int", vec![term("0")]),
        // Refinement downcasts: PosInt ::= Int, NegInt ::= Int.
        rule("IntToPos", "PosInt", vec![nonterm("Int", "i")]),
        rule("IntToNeg", "NegInt", vec![nonterm("Int", "i")]),
        // Numeric casts into Proc.
        rule("ProcInt", "Proc", vec![nonterm("Int", "i")]),
        rule("ProcPos", "Proc", vec![nonterm("PosInt", "p")]),
    ];
    let refinement_types = vec![refinement("PosInt", "Int"), refinement("NegInt", "Int")];
    (all_syntax, categories, refinement_types)
}

/// The cast rules in the fixture, paired with their source category — the
/// expected `(label, src)` set the agreement assertion iterates.
fn expected_casts() -> Vec<(&'static str, &'static str)> {
    vec![
        ("IntToPos", "Int"),
        ("IntToNeg", "Int"),
        ("ProcInt", "Int"),
        ("ProcPos", "PosInt"),
    ]
}

// ══════════════════════════════════════════════════════════════════════════════
// The agreement assertion
// ══════════════════════════════════════════════════════════════════════════════

/// For each cast `r : src → tgt`, assert its transducer pre-image is
/// language-equivalent to the Phase-2 source `category_automaton(src)`.
#[test]
fn preimage_agrees_with_source_category_automaton() {
    let (all_syntax, categories, _refinement) = refinement_cast_fixture();
    let alpha = ranked_alphabet(&all_syntax, &categories);
    let elem = build_tree_algebra(&alpha);

    for (label, src) in expected_casts() {
        let preimage = cast_preimage_automaton(label, &all_syntax, &categories)
            .unwrap_or_else(|| panic!("cast `{label}` must have a pre-image automaton"));
        let source_auto = category_automaton(src, &alpha, &elem);

        assert!(
            languages_equal(&preimage, &source_auto),
            "transducer pre-image of cast `{label}` diverged from the Phase-2 \
             `category_automaton` of its source `{src}` (the `.0` transducer MUST \
             agree category-for-category — a disagreement is a real finding, not \
             to be papered over)"
        );
    }
}

/// The analysis is well-formed and consistent with directly recomputing its
/// predicates from the Phase-2 automata: every `(src, _)` in `non_total_casts`
/// reflects a genuinely non-total transducer, and `dead_casts` reflects a
/// genuinely empty pre-image ∩ source intersection.
#[test]
fn analysis_is_self_consistent() {
    let (all_syntax, categories, refinement) = refinement_cast_fixture();
    let alpha = ranked_alphabet(&all_syntax, &categories);
    let elem = build_tree_algebra(&alpha);

    let analysis = analyze_from_bundle(&all_syntax, &categories, &refinement);

    // Recompute the `dead_casts` predicate independently: pre-image ∩ source
    // category empty. None of the fixture casts are dead (every source category
    // — Int, PosInt — is inhabited and cast-reachable), so `dead_casts` is empty.
    for (label, src) in expected_casts() {
        let preimage =
            cast_preimage_automaton(label, &all_syntax, &categories).expect("cast has a pre-image");
        let source_auto = category_automaton(src, &alpha, &elem);
        let intersection_empty = preimage.intersect(&source_auto).is_empty();
        assert_eq!(
            analysis.dead_casts.contains(&label.to_string()),
            intersection_empty,
            "`dead_casts` membership for `{label}` must equal the (pre-image ∩ source) emptiness"
        );
    }
    assert!(
        analysis.dead_casts.is_empty(),
        "no fixture cast is dead (all source categories inhabited + reachable): {:?}",
        analysis.dead_casts
    );

    // Every fixture cast is NON-total (a cast applies only to its source
    // category, never to *every* well-formed term over the alphabet), so each
    // appears in `non_total_casts`.
    assert_eq!(
        analysis.non_total_casts.len(),
        expected_casts().len(),
        "every fixture cast should be non-total: {:?}",
        analysis.non_total_casts
    );
    for (_, src) in expected_casts() {
        assert!(
            analysis.non_total_casts.iter().any(|(s, _)| s == src),
            "source `{src}` must appear among the non-total casts: {:?}",
            analysis.non_total_casts
        );
    }
}

/// Non-degeneracy guard: the fixture must actually contain casts (so the
/// agreement proof is non-trivial), and the source categories must be inhabited
/// (so the pre-image is non-empty — agreement on two empty languages would be
/// vacuous).
#[test]
fn fixture_exercises_inhabited_casts() {
    let (all_syntax, categories, _refinement) = refinement_cast_fixture();
    let alpha = ranked_alphabet(&all_syntax, &categories);
    let elem = build_tree_algebra(&alpha);

    assert!(!expected_casts().is_empty(), "fixture must contain cast rules");

    for (label, src) in expected_casts() {
        let preimage =
            cast_preimage_automaton(label, &all_syntax, &categories).expect("cast has a pre-image");
        assert!(
            !preimage.is_empty(),
            "cast `{label}` pre-image (source `{src}`) must be non-empty — else agreement is vacuous"
        );
        // And the Phase-2 source automaton is independently non-empty too.
        let source_auto = category_automaton(src, &alpha, &elem);
        assert!(
            !source_auto.is_empty(),
            "Phase-2 `category_automaton({src})` must be non-empty (inhabited source)"
        );
    }
}

#[test]
#[ignore = "evidence dump only"]
fn dump_transducer_evidence() {
    let (all_syntax, categories, refinement) = refinement_cast_fixture();
    let analysis = analyze_from_bundle(&all_syntax, &categories, &refinement);
    eprintln!("[refinement_cast]");
    eprintln!("  non_total_casts = {:?}", analysis.non_total_casts);
    eprintln!("  dead_casts      = {:?}", analysis.dead_casts);
    for (label, src) in expected_casts() {
        let preimage =
            cast_preimage_automaton(label, &all_syntax, &categories).expect("cast has a pre-image");
        let alpha = ranked_alphabet(&all_syntax, &categories);
        let elem = build_tree_algebra(&alpha);
        let source_auto = category_automaton(src, &alpha, &elem);
        eprintln!(
            "  cast {label}: src={src}  preimage≡category={}",
            languages_equal(&preimage, &source_auto)
        );
    }
}
