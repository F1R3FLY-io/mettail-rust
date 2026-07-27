//! Agreement snapshot for the OSLF substrate Phase 4 `.0`-inert bisimulation
//! partition-refinement engine (`bisimulation::analyze_from_bundle`).
//!
//! The single-LTS partition-refinement engine must produce a per-category
//! bisimulation partition that **agrees category-for-category** with the live
//! `alternating::analyze_from_bundle` pairwise-game engine over the *same*
//! grammar bundle — that is the `.0`-inert contract and the agreement gate that
//! authorizes the `.1` supersede (routing the AWA bisimulation dispatch through
//! this engine). The `bisimulation` engine merely *re-derives* the same
//! `non_bisimilar_pairs` by Kanellakis–Smolka / Paige–Tarjan refinement of one
//! `Lts` rather than by the pairwise alternating game; it must not change a
//! single category-pair verdict.
//!
//! ## What is compared
//!
//! For each fixture grammar, both engines consume the **identical** bundle
//! (`all_syntax` + `categories`) and return a `non_bisimilar_pairs:
//! Vec<(String, String)>`. The two are compared as *normalized sets* of
//! unordered category pairs (so a different enumeration order is not a spurious
//! failure), and on any disagreement the precise per-pair diff is printed and
//! the test FAILS — a genuine disagreement is a real finding, never papered over
//! by adjusting the expectation.
//!
//! The fixtures mirror the `languages/` corpus grammars (calculator, lambda,
//! rholang, ambient, guarded_rho), constructed with the same tiny
//! `term`/`nonterm`/`rule` bundle helpers the sibling `.0` snapshot tests
//! (`sym_tree_structural_snapshot.rs`, `guard_carrier_snapshot.rs`) use.

use std::collections::BTreeSet;

use mettail_prattail::alternating;
use mettail_prattail::bisimulation;
use mettail_prattail::grammar::ir::CollectionKind;
use mettail_prattail::pipeline::CategoryInfo;
use mettail_prattail::SyntaxItemSpec;

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
fn binder(name: &str, cat: &str, is_multi: bool) -> SyntaxItemSpec {
    SyntaxItemSpec::Binder {
        param_name: name.to_string(),
        category: cat.to_string(),
        is_multi,
    }
}
fn bag_collection(name: &str, elem_cat: &str, sep: &str) -> SyntaxItemSpec {
    SyntaxItemSpec::Collection {
        param_name: name.to_string(),
        element_category: elem_cat.to_string(),
        separator: sep.to_string(),
        kind: CollectionKind::HashBag,
        key_val_separator: None,
    }
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

// ══════════════════════════════════════════════════════════════════════════════
// The agreement assertion
// ══════════════════════════════════════════════════════════════════════════════

/// Normalize a `non_bisimilar_pairs` list into a set of *unordered* category
/// pairs (so a `(A, B)` vs `(B, A)` enumeration difference is not a failure).
fn normalized(pairs: &[(String, String)]) -> BTreeSet<(String, String)> {
    pairs
        .iter()
        .map(|(a, b)| {
            if a <= b {
                (a.clone(), b.clone())
            } else {
                (b.clone(), a.clone())
            }
        })
        .collect()
}

/// The agreement assertion: the `bisimulation` engine's non-bisimilar-pair set
/// equals the `alternating` engine's, with a precise per-pair diff on failure.
fn assert_agrees(name: &str, all_syntax: &[SyntaxRule], categories: &[CategoryInfo]) {
    let bisim = bisimulation::analyze_from_bundle(all_syntax, categories);
    let alt = alternating::analyze_from_bundle(all_syntax, categories);

    let bisim_set = normalized(&bisim.non_bisimilar_pairs);
    let alt_set = normalized(&alt.non_bisimilar_pairs);

    if bisim_set != alt_set {
        let only_bisim: Vec<&(String, String)> =
            bisim_set.iter().filter(|p| !alt_set.contains(*p)).collect();
        let only_alt: Vec<&(String, String)> =
            alt_set.iter().filter(|p| !bisim_set.contains(*p)).collect();
        panic!(
            "bisimulation engine diverged from alternating engine for `{name}` \
             (the `.0` engine MUST agree category-for-category — a disagreement \
             is a real finding, not to be papered over):\n  \
             bisimulation non-bisimilar : {bisim_set:?}\n  \
             alternating  non-bisimilar : {alt_set:?}\n  \
             only in bisimulation       : {only_bisim:?}\n  \
             only in alternating        : {only_alt:?}"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Fixtures (mirror the `languages/` corpus grammars)
// ══════════════════════════════════════════════════════════════════════════════

/// Calculator: a `Proc` super-category, scalar `Int`/`Bool`/`Str`, two
/// collection containers, and arithmetic / cast / variable rules.
fn calculator_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
    let categories = vec![
        struct_cat("Proc", true, true),
        scalar_cat("Int", "i32"),
        scalar_cat("Bool", "bool"),
        scalar_cat("Str", "str"),
        struct_cat("List", false, false),
        struct_cat("Bag", false, false),
    ];
    let all_syntax = vec![
        rule("IVar", "Int", vec![ident("x")]),
        rule("BVar", "Bool", vec![ident("x")]),
        rule("ProcInt", "Proc", vec![nonterm("Int", "i")]),
        rule("ProcBool", "Proc", vec![nonterm("Bool", "b")]),
        rule("ProcStr", "Proc", vec![nonterm("Str", "s")]),
        rule("AddInt", "Int", vec![nonterm("Int", "a"), term("+"), nonterm("Int", "b")]),
        rule(
            "FloatToInt",
            "Int",
            vec![term("int"), term("("), nonterm("Str", "a"), term(")")],
        ),
        rule("Fact", "Int", vec![nonterm("Int", "a"), term("!")]),
        rule("BagLit", "Bag", vec![bag_collection("xs", "Proc", "|")]),
    ];
    (all_syntax, categories)
}

/// Lambda calculus: a single `Term` category with a variable, the binder-led
/// `Lam` (`^x.Term`), and the application `App(Term, Term)`. The
/// single-category case (no pair to split) plus a scalar-free binder grammar.
fn lambda_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
    let categories = vec![struct_cat("Term", true, true)];
    let all_syntax = vec![
        rule("Var", "Term", vec![ident("x")]),
        rule("Lam", "Term", vec![binder("x", "Term", false), nonterm("Term", "body")]),
        rule("App", "Term", vec![nonterm("Term", "f"), nonterm("Term", "a")]),
    ];
    (all_syntax, categories)
}

/// Rholang: `Proc`/`Name` process categories + scalar `Int`, with the constant
/// `PZero`, the mixfix `POutput`, the binder-led `PNew`, a scalar cast, and the
/// collection-led `PPar`.
fn rholang_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
    let categories = vec![
        struct_cat("Proc", true, true),
        struct_cat("Name", false, true),
        scalar_cat("Int", "i64"),
        struct_cat("List", false, false),
        struct_cat("Bag", false, false),
    ];
    let all_syntax = vec![
        rule("PZero", "Proc", vec![term("{}")]),
        rule("PDrop", "Proc", vec![term("*"), term("("), nonterm("Name", "n"), term(")")]),
        rule("PPar", "Proc", vec![term("{"), bag_collection("ps", "Proc", "|"), term("}")]),
        rule(
            "POutput",
            "Proc",
            vec![nonterm("Name", "n"), term("!"), term("("), nonterm("Proc", "q"), term(")")],
        ),
        rule("NQuote", "Name", vec![term("@"), term("("), nonterm("Proc", "p"), term(")")]),
        rule("PNew", "Proc", vec![binder("xs", "Name", true), nonterm("Proc", "p")]),
        rule("CastInt", "Proc", vec![nonterm("Int", "k")]),
        rule("IVar", "Int", vec![ident("x")]),
    ];
    (all_syntax, categories)
}

/// Ambient: `Proc` and `Name` only, both non-scalar (the "no scalar sorts"
/// stress case).
fn ambient_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
    let categories = vec![struct_cat("Proc", true, true), struct_cat("Name", false, true)];
    let all_syntax = vec![
        rule("PZero", "Proc", vec![term("0")]),
        rule(
            "PIn",
            "Proc",
            vec![term("in("), nonterm("Name", "n"), term(","), nonterm("Proc", "p"), term(")")],
        ),
        rule(
            "PAmb",
            "Proc",
            vec![nonterm("Name", "n"), term("["), nonterm("Proc", "p"), term("]")],
        ),
        rule("PNew", "Proc", vec![binder("x", "Name", false), nonterm("Proc", "p")]),
        rule("PPar", "Proc", vec![term("{"), bag_collection("ps", "Proc", "|"), term("}")]),
        rule("NVar", "Name", vec![ident("x")]),
    ];
    (all_syntax, categories)
}

/// GuardedRho: a Rho-style calculus with a `Proc`/`Name` split plus a `Bool`
/// guard scalar and a guarded receive. Exercises a scalar category alongside the
/// process categories.
fn guarded_rho_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
    let categories = vec![
        struct_cat("Proc", true, true),
        struct_cat("Name", false, true),
        scalar_cat("Bool", "bool"),
    ];
    let all_syntax = vec![
        rule("PZero", "Proc", vec![term("0")]),
        rule(
            "POut",
            "Proc",
            vec![nonterm("Name", "n"), term("!"), term("("), nonterm("Proc", "q"), term(")")],
        ),
        rule(
            "PGuardedIn",
            "Proc",
            vec![
                term("for"),
                term("("),
                binder("x", "Name", false),
                term("<-"),
                nonterm("Name", "n"),
                term("if"),
                nonterm("Bool", "g"),
                term(")"),
                nonterm("Proc", "p"),
            ],
        ),
        rule("NQuote", "Name", vec![term("@"), term("("), nonterm("Proc", "p"), term(")")]),
        rule("BTrue", "Bool", vec![term("true")]),
        rule("BVar", "Bool", vec![ident("b")]),
    ];
    (all_syntax, categories)
}

// ══════════════════════════════════════════════════════════════════════════════
// The agreement assertions
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn calculator_agrees() {
    let (all_syntax, categories) = calculator_fixture();
    assert_agrees("calculator", &all_syntax, &categories);
}

#[test]
fn lambda_agrees() {
    let (all_syntax, categories) = lambda_fixture();
    assert_agrees("lambda", &all_syntax, &categories);
}

#[test]
fn rholang_agrees() {
    let (all_syntax, categories) = rholang_fixture();
    assert_agrees("rholang", &all_syntax, &categories);
}

#[test]
fn ambient_agrees() {
    let (all_syntax, categories) = ambient_fixture();
    assert_agrees("ambient", &all_syntax, &categories);
}

#[test]
fn guarded_rho_agrees() {
    let (all_syntax, categories) = guarded_rho_fixture();
    assert_agrees("guarded_rho", &all_syntax, &categories);
}

/// Non-degeneracy guard: the multi-category fixtures must actually produce at
/// least one non-bisimilar pair (distinct categories with distinct rule labels),
/// so the agreement proof never degenerates into "two empty partitions trivially
/// match". If a future edit makes the fixtures trivial, this fails loudly.
#[test]
fn fixtures_exercise_non_bisimilar_pairs() {
    for (name, (rules, cats)) in [
        ("calculator", calculator_fixture()),
        ("rholang", rholang_fixture()),
        ("ambient", ambient_fixture()),
        ("guarded_rho", guarded_rho_fixture()),
    ] {
        let bisim = bisimulation::analyze_from_bundle(&rules, &cats);
        assert!(
            !bisim.non_bisimilar_pairs.is_empty(),
            "multi-category fixture `{name}` must produce at least one non-bisimilar pair \
             (else the agreement proof is degenerate): {:?}",
            bisim.non_bisimilar_pairs
        );
        // And the alternating engine must independently witness non-emptiness too.
        let alt = alternating::analyze_from_bundle(&rules, &cats);
        assert!(
            !alt.non_bisimilar_pairs.is_empty(),
            "alternating engine must independently witness non-bisimilar pairs for `{name}`"
        );
    }

    // The single-category lambda fixture has NO pair, so both engines yield the
    // empty partition — a real (degenerate) agreement that the set comparison
    // still validates.
    let (ls, lc) = lambda_fixture();
    assert!(
        bisimulation::analyze_from_bundle(&ls, &lc)
            .non_bisimilar_pairs
            .is_empty(),
        "single-category lambda has no category pair ⇒ empty non-bisimilar set"
    );
}
