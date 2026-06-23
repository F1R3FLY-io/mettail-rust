//! Snapshot for the OSLF substrate Phase 6 `.1` live Hindley-Milner **base-sort
//! consistency** analysis (`hindley_milner::analyze_from_bundle`).
//!
//! ## What this gate proves
//!
//! 1. **PARITY (inertness + correctness).** Over every existing grammar fixture
//!    (calculator / lambda / rhocalc / ambient / guarded_rho),
//!    `hindley_milner::analyze_from_bundle`:
//!      - reports NO `sort_mismatches` (every field category is declared ⇒ the
//!        inferred constructor arrow unifies with the declared arrow);
//!      - infers, for each rule, exactly the constructor arrow
//!        `Arrow(field_sort_1, …Arrow(field_sort_n, Mono(declared_category)))`,
//!        so the inferred *result* sort equals the rule's declared category; and
//!      - introduces NO `HmType::Var` (the no-fresh-vars determinism invariant —
//!        the pass touches only `Mono`/`Arrow` and never the global
//!        `fresh_type_var` counter).
//!
//! 2. **POSITIVE (the live decision actually fires).** A hand-built bundle with a
//!    deliberate sort clash — a constructor whose field references a category
//!    that is NOT declared, so it cannot `unify` with its declared use — yields
//!    EXACTLY ONE `sort_mismatch`, whose `(label, reason)` is checked against a
//!    HAND-COMPUTED expectation.
//!
//! The parity result/no-Var checks are made by reconstructing each rule's
//! expected arrow from `Mono` leaves only and asserting the production pass
//! renders the byte-identical arrow — so enabling `oslf-hindley-milner` cannot
//! change the analysis of any grammar today.
//!
//! On any mismatch the test FAILS LOUDLY with the observed value; the expected
//! verdict is never adjusted to match buggy output (per the project's
//! "never weaken a test" discipline).

#![cfg(feature = "oslf-hindley-milner")]

use mettail_prattail::grammar::ir::CollectionKind;
use mettail_prattail::hindley_milner::{self, HmType};
use mettail_prattail::pipeline::CategoryInfo;
use mettail_prattail::SyntaxItemSpec;

// ── Tiny constructors for readable fixtures (mirror the sibling `.0` snapshots) ─

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
// Independent re-derivation of the expected constructor arrow (test side)
// ══════════════════════════════════════════════════════════════════════════════

/// Collect a rule body's **field sorts** as `HmType::Mono(category)` leaves,
/// left-to-right, descending the structural wrappers exactly as the production
/// `hindley_milner::collect_field_sorts` does. Re-derived independently here (the
/// production helper is private) so the parity assertion is a genuine cross-check
/// rather than a tautology. Every leaf is `Mono` — there is intentionally NO
/// `HmType::Var` arm, so if the production pass ever injected a fresh var the
/// rendered strings would diverge and the parity test would fail.
fn expected_field_sorts(items: &[SyntaxItemSpec], out: &mut Vec<HmType>) {
    for item in items {
        match item {
            SyntaxItemSpec::NonTerminal { category, .. } => {
                out.push(HmType::Mono(category.clone()))
            },
            SyntaxItemSpec::Binder { category, .. } => out.push(HmType::Mono(category.clone())),
            SyntaxItemSpec::Collection { element_category, .. } => {
                out.push(HmType::Mono(element_category.clone()))
            },
            SyntaxItemSpec::Optional { inner } => expected_field_sorts(inner, out),
            SyntaxItemSpec::Sep { body, .. } => {
                expected_field_sorts(std::slice::from_ref(body.as_ref()), out)
            },
            SyntaxItemSpec::Map { body_items } => expected_field_sorts(body_items, out),
            SyntaxItemSpec::Zip { body, .. } => {
                expected_field_sorts(std::slice::from_ref(body.as_ref()), out)
            },
            // Terminal, IdentCapture, BinderCollection, … — no field sort.
            _ => {},
        }
    }
}

/// Build the expected constructor arrow `Arrow(f1, …Arrow(fn, Mono(category)))`
/// from `Mono` leaves only, then render it via the same notation the production
/// pass uses (right-associated `a → b → c`, parenthesizing nested arrow domains).
fn expected_arrow_rendered(category: &str, items: &[SyntaxItemSpec]) -> String {
    let mut fields: Vec<HmType> = Vec::new();
    expected_field_sorts(items, &mut fields);
    let mut acc = HmType::Mono(category.to_string());
    for field in fields.iter().rev() {
        acc = HmType::Arrow(Box::new(field.clone()), Box::new(acc));
    }
    render_local(&acc)
}

/// Local mirror of the production `render_hm_type` (private), so the test owns
/// its expectation end-to-end.
fn render_local(ty: &HmType) -> String {
    match ty {
        HmType::Var(v) => v.clone(),
        HmType::Mono(m) => m.clone(),
        HmType::Arrow(a, b) => {
            let left = match a.as_ref() {
                HmType::Arrow(..) => format!("({})", render_local(a)),
                other => render_local(other),
            };
            format!("{left} → {}", render_local(b))
        },
        HmType::Forall(vars, body) => format!("∀{}. {}", vars.join(" "), render_local(body)),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Fixtures (mirror the `languages/` corpus grammars — identical to the
// bisimulation agreement snapshot fixtures)
// ══════════════════════════════════════════════════════════════════════════════

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

fn lambda_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
    let categories = vec![struct_cat("Term", true, true)];
    let all_syntax = vec![
        rule("Var", "Term", vec![ident("x")]),
        rule("Lam", "Term", vec![binder("x", "Term", false), nonterm("Term", "body")]),
        rule("App", "Term", vec![nonterm("Term", "f"), nonterm("Term", "a")]),
    ];
    (all_syntax, categories)
}

fn rhocalc_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
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
// (a) PARITY — inert + correct over the corpus fixtures
// ══════════════════════════════════════════════════════════════════════════════

/// The parity assertion: NO mismatches, and every constructor's inferred arrow is
/// the all-`Mono`-leaf arrow with result `Mono(declared_category)` — which proves
/// (i) the inferred result sort equals the declared category, and (ii) the pass
/// introduced no `HmType::Var` (an all-`Mono` reconstruction renders identically
/// iff the production pass also used only `Mono`/`Arrow`).
fn assert_inert_and_correct(name: &str, all_syntax: &[SyntaxRule], categories: &[CategoryInfo]) {
    let analysis = hindley_milner::analyze_from_bundle(all_syntax, categories);

    assert!(
        analysis.sort_mismatches.is_empty(),
        "well-formed grammar `{name}` must produce NO base-sort mismatches \
         (a non-empty `sort_mismatches` is a real finding, never papered over): {:?}",
        analysis.sort_mismatches
    );

    // One inferred constructor type per rule, in `all_syntax` order.
    assert_eq!(
        analysis.inferred_constructor_types.len(),
        all_syntax.len(),
        "fixture `{name}`: every rule must yield exactly one inferred constructor type"
    );

    for ((got_label, got_rendered), (exp_label, exp_cat, items)) in analysis
        .inferred_constructor_types
        .iter()
        .zip(all_syntax.iter())
    {
        assert_eq!(
            got_label, exp_label,
            "fixture `{name}`: inferred-type ordering must match `all_syntax` ordering"
        );
        let expected = expected_arrow_rendered(exp_cat, items);
        assert_eq!(
            got_rendered, &expected,
            "fixture `{name}` rule `{got_label}`: inferred constructor arrow must equal the \
             all-Mono reconstruction with result sort = declared category `{exp_cat}` \
             (proves result==category AND no fresh `HmType::Var`)"
        );
        // Redundant-but-explicit: the rendered arrow's codomain (rightmost atom)
        // is exactly the declared category, and it contains no fresh-var token.
        let codomain = got_rendered.rsplit(" → ").next().unwrap_or(got_rendered);
        assert_eq!(
            codomain, exp_cat,
            "fixture `{name}` rule `{got_label}`: result sort must be the declared category"
        );
        assert!(
            !contains_fresh_var(got_rendered),
            "fixture `{name}` rule `{got_label}`: inferred type `{got_rendered}` must contain \
             no fresh `HmType::Var` (`t<n>`) — the determinism invariant"
        );
    }
}

/// A fresh type variable rendered by `fresh_type_var` is `t<digits>`; the
/// base-sort pass must never emit one. (Category names in the fixtures are
/// PascalCase, so this never false-positives.)
fn contains_fresh_var(rendered: &str) -> bool {
    rendered
        .split(|c: char| !c.is_ascii_alphanumeric())
        .any(|tok| {
            let mut chars = tok.chars();
            matches!(chars.next(), Some('t')) && {
                let rest: String = chars.collect();
                !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
            }
        })
}

#[test]
fn calculator_inert() {
    let (all_syntax, categories) = calculator_fixture();
    assert_inert_and_correct("calculator", &all_syntax, &categories);
}

#[test]
fn lambda_inert() {
    let (all_syntax, categories) = lambda_fixture();
    assert_inert_and_correct("lambda", &all_syntax, &categories);
}

#[test]
fn rhocalc_inert() {
    let (all_syntax, categories) = rhocalc_fixture();
    assert_inert_and_correct("rhocalc", &all_syntax, &categories);
}

#[test]
fn ambient_inert() {
    let (all_syntax, categories) = ambient_fixture();
    assert_inert_and_correct("ambient", &all_syntax, &categories);
}

#[test]
fn guarded_rho_inert() {
    let (all_syntax, categories) = guarded_rho_fixture();
    assert_inert_and_correct("guarded_rho", &all_syntax, &categories);
}

/// Non-degeneracy guard: the multi-field fixtures must actually exercise arrows
/// with ≥1 domain (a constructor with at least one field sort), so "no mismatch"
/// is a real inert verdict over non-trivial arrows rather than a vacuous pass
/// over nullary constructors only.
#[test]
fn fixtures_exercise_nonnullary_arrows() {
    for (name, (rules, cats)) in [
        ("calculator", calculator_fixture()),
        ("lambda", lambda_fixture()),
        ("rhocalc", rhocalc_fixture()),
        ("ambient", ambient_fixture()),
        ("guarded_rho", guarded_rho_fixture()),
    ] {
        let analysis = hindley_milner::analyze_from_bundle(&rules, &cats);
        let any_arrow = analysis
            .inferred_constructor_types
            .iter()
            .any(|(_, rendered)| rendered.contains(" → "));
        assert!(
            any_arrow,
            "fixture `{name}` must exercise at least one non-nullary constructor arrow \
             (else the inertness proof is degenerate): {:?}",
            analysis.inferred_constructor_types
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// (b) POSITIVE — a deliberate base-sort clash yields exactly one mismatch
// ══════════════════════════════════════════════════════════════════════════════

/// A hand-built bundle whose single multi-field rule references an UNDECLARED
/// category (`Ghost`) in a field position — so the inferred field sort
/// `Mono("Ghost")` cannot unify with the declared-side sentinel
/// `Mono("⊥undeclared:Ghost")`, and the constructor's inferred result sort thus
/// disagrees with a consistent typing. Exactly one `sort_mismatch` must be
/// reported, with the hand-computed `(label, reason)`.
#[test]
fn positive_undeclared_field_category_is_one_mismatch() {
    // `A` and `B` are declared; `Ghost` is deliberately NOT declared.
    let categories = vec![struct_cat("A", true, true), struct_cat("B", false, true)];
    let all_syntax = vec![
        // A well-formed control rule: every field category (`B`) is declared ⇒
        // no mismatch, so the positive verdict is isolated to the bad rule.
        rule("Good", "A", vec![nonterm("B", "b")]),
        // The clashing rule: field references the undeclared `Ghost`.
        rule("Bad", "A", vec![nonterm("Ghost", "g")]),
    ];

    let analysis = hindley_milner::analyze_from_bundle(&all_syntax, &categories);

    // Exactly one mismatch, for `Bad`.
    assert_eq!(
        analysis.sort_mismatches.len(),
        1,
        "exactly one base-sort mismatch expected (the `Bad` rule); got: {:?}",
        analysis.sort_mismatches
    );
    let (label, reason) = &analysis.sort_mismatches[0];
    assert_eq!(label, "Bad", "the mismatch must be reported against the `Bad` rule");

    // Hand-computed reason:
    //   inferred arrow  = Arrow(Mono("Ghost"), Mono("A"))      renders "Ghost → A"
    //   declared arrow  = Arrow(Mono("⊥undeclared:Ghost"), Mono("A"))
    //   unify recurses into the domain first:
    //     unify(Mono("Ghost"), Mono("⊥undeclared:Ghost"))
    //       = Err(UnificationFailure{ left: Mono("Ghost"), right: Mono("⊥undeclared:Ghost") })
    //   whose Display is:
    //     HM unification failure: cannot unify Mono("Ghost") with Mono("⊥undeclared:Ghost")
    let expected_reason = "inferred constructor type Ghost → A disagrees with its declaration: \
         HM unification failure: cannot unify Mono(\"Ghost\") with Mono(\"⊥undeclared:Ghost\")";
    assert_eq!(
        reason, expected_reason,
        "the mismatch reason must match the hand-computed unification failure"
    );

    // The well-formed control rule must still be inferred (and appear in the
    // evidence list), proving the clash did not poison the whole bundle.
    assert!(
        analysis
            .inferred_constructor_types
            .iter()
            .any(|(l, r)| l == "Good" && r == "B → A"),
        "the well-formed `Good` rule must still infer `B → A`: {:?}",
        analysis.inferred_constructor_types
    );
    // The `Bad` rule, having failed unification, must NOT appear among the
    // successfully-inferred constructor types.
    assert!(
        !analysis
            .inferred_constructor_types
            .iter()
            .any(|(l, _)| l == "Bad"),
        "the clashing `Bad` rule must not appear among inferred constructor types"
    );
}
