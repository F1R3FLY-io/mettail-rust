//! Snapshot for the OSLF substrate Phase 5 `.1` live `letprop` recursive-predicate
//! → modal-μ-calculus → Parity Alternating Tree Automaton (PATA) decision path.
//!
//! ## What this gate proves
//!
//! 1. **PARITY (inertness).** Over every existing grammar fixture
//!    (calculator / lambda / rhocalc / ambient / guarded_rho),
//!    `parity_tree::analyze_recursive_predicates` returns a result EQUIVALENT to
//!    today's stub `analyze_from_bundle` — specifically an EMPTY
//!    `fixpoint_decisions` and the identical headline fields (`num_states`,
//!    `max_priority`, `is_empty`, `priority_depth`). No current grammar surface
//!    syntax produces a `letprop` recursive predicate (that is a tracked
//!    follow-up touching `ast/`), so the live path finds NONE and is parity-safe.
//!    This is the `.1`-wire contract: enabling `oslf-letprop` cannot change the
//!    analysis of any grammar that exists today.
//!
//! 2. **POSITIVE (the live decision actually runs).** A SYNTHETIC
//!    `RecursivePredicate` is constructed directly via the `letprop` API (exactly
//!    as `letprop.rs`'s own unit tests do) and decided through
//!    `parity_tree::decide_recursive_predicate` — which lowers it through
//!    `letprop::letprop_to_pata` (giving that SHIPPED bridge its FIRST real
//!    caller) and decides (non-)emptiness via the Zielonka-aligned
//!    `parity_tree::check_emptiness`. The PATA shape (`num_states > 0`) and the
//!    satisfiability verdict are checked against a HAND-COMPUTED expectation.
//!
//! On any mismatch the test FAILS LOUDLY with the observed value; the expected
//! verdict is never adjusted to match buggy output (per the project's
//! "never weaken a test" discipline).

#![cfg(feature = "oslf-letprop")]

use mettail_prattail::grammar::ir::CollectionKind;
use mettail_prattail::letprop::{LetPropExpr, RecursivePredicate};
use mettail_prattail::parity_tree;
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

// ── `letprop` body constructors (mirror `letprop.rs`'s own unit-test helpers) ──

fn rec(args: &[&str]) -> LetPropExpr {
    LetPropExpr::Recursive {
        args: args.iter().map(|s| s.to_string()).collect(),
    }
}
fn atom(name: &str, args: &[&str]) -> LetPropExpr {
    LetPropExpr::Atom {
        relation: name.to_string(),
        args: args.iter().map(|s| s.to_string()).collect(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Fixtures (mirror the `languages/` corpus grammars)
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
        rule("FloatToInt", "Int", vec![term("int"), term("("), nonterm("Str", "a"), term(")")]),
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
        rule("PAmb", "Proc", vec![nonterm("Name", "n"), term("["), nonterm("Proc", "p"), term("]")]),
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

fn all_fixtures() -> Vec<(&'static str, (Vec<SyntaxRule>, Vec<CategoryInfo>))> {
    vec![
        ("calculator", calculator_fixture()),
        ("lambda", lambda_fixture()),
        ("rhocalc", rhocalc_fixture()),
        ("ambient", ambient_fixture()),
        ("guarded_rho", guarded_rho_fixture()),
    ]
}

// ══════════════════════════════════════════════════════════════════════════════
// (a) PARITY: the live path is inert on every present grammar
// ══════════════════════════════════════════════════════════════════════════════

/// `analyze_recursive_predicates` must agree with the stub `analyze_from_bundle`
/// on every existing grammar, and report an EMPTY `fixpoint_decisions` — proving
/// the `.1`-wire is parity-safe (enabling the feature changes nothing for any
/// grammar that exists today, because none carries a `letprop` recursive
/// predicate).
#[test]
fn live_path_is_inert_on_all_fixtures() {
    for (name, (all_syntax, categories)) in all_fixtures() {
        let stub = parity_tree::analyze_from_bundle(&all_syntax, &categories);
        let live = parity_tree::analyze_recursive_predicates(&all_syntax, &categories);

        assert!(
            live.fixpoint_decisions.is_empty(),
            "fixture `{name}`: no surface syntax produces a recursive predicate, so the live \
             path MUST find none — got fixpoint_decisions = {:?}",
            live.fixpoint_decisions
        );

        // Headline fields must be byte-equivalent to the stub (the only delta is
        // the new empty field), so PT01–PT03 verdicts are unchanged.
        assert_eq!(
            (stub.num_states, stub.max_priority, stub.is_empty, stub.priority_depth),
            (live.num_states, live.max_priority, live.is_empty, live.priority_depth),
            "fixture `{name}`: live recursive-predicate analysis diverged from the stub on the \
             headline PATA summary (it must be identical when no recursive predicate is present)"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// (b) POSITIVE: the live decision runs end-to-end on a synthetic predicate
// ══════════════════════════════════════════════════════════════════════════════

/// `reachable(x, y) = edge(x, y) ∨ reachable(x, y)`.
///
/// Hand computation (matching `parity_tree::try_mu_calculus_to_pata` /
/// `compile_formula` / `check_emptiness`):
///
/// - Positive polarity (the recursive call is not under `Not`) ⇒ least fixpoint
///   `μ reachable. (atom:edge ∨ reachable)`.
/// - `compile_formula` allocates the `Mu` state FIRST: existential, priority
///   `0 | 1 = 1` (odd). Then the body `Or` compiles `Atom("edge")` (existential,
///   priority 0, EVEN) and `Var("reachable")` (resolves to the `Mu` state), then
///   the `Or` state (existential, priority 0, EVEN). The `Mu` state's transition
///   targets the `Or` state.
/// - `check_emptiness` seeds every even-priority state as accepting: the `Atom`
///   and `Or` states start accepting; the odd-priority `Mu` (initial) state does
///   not. The `Mu` state is existential with one transition to the (accepting)
///   `Or` state ⇒ it becomes accepting. Initial state accepting ⇒ `L ≠ ∅`.
///
/// ⇒ SATISFIABLE (`decide_recursive_predicate == true`,
/// `check_emptiness == false`), and the PATA has `num_states > 0`.
fn reachable_predicate() -> RecursivePredicate {
    RecursivePredicate {
        name: "reachable".to_string(),
        params: vec!["x".to_string(), "y".to_string()],
        body: LetPropExpr::Or(Box::new(atom("edge", &["x", "y"])), Box::new(rec(&["x", "y"]))),
    }
}

/// `spin = spin` — a least fixpoint with NO base case (pure self-recursion).
///
/// Hand computation:
///
/// - Positive polarity ⇒ `μ spin. spin`. `compile_formula` allocates the `Mu`
///   state (existential, odd priority 1) and binds `spin` to it; the body
///   `Var("spin")` resolves back to that same state, so the `Mu` state's
///   transition is a SELF-LOOP to an odd-priority state.
/// - `check_emptiness`: the lone state has odd priority ⇒ not seeded accepting;
///   its only transition targets itself, which is not (yet) accepting, so the
///   fixpoint never flips it. Initial state not accepting ⇒ `L = ∅`.
///
/// ⇒ UNSATISFIABLE (`decide_recursive_predicate == false`,
/// `check_emptiness == true`) — a dead behavioral type that LP01 would flag.
fn spin_predicate() -> RecursivePredicate {
    RecursivePredicate {
        name: "spin".to_string(),
        params: vec![],
        body: rec(&[]),
    }
}

#[test]
fn positive_reachable_is_satisfiable() {
    let pred = reachable_predicate();

    // The SHIPPED bridge gets its first real caller here.
    let pata = mettail_prattail::letprop::letprop_to_pata(&pred, pred.params.len().max(1))
        .expect("reachable predicate must lower to a PATA");
    assert!(
        pata.num_states() > 0,
        "the `reachable` least-fixpoint must compile to a non-trivial PATA (got 0 states)"
    );

    // Non-emptiness (satisfiability) decided by the Zielonka-aligned checker.
    assert!(
        !parity_tree::check_emptiness(&pata),
        "`reachable = edge ∨ reachable` has the reachable base atom `edge`, so its PATA must be \
         NON-empty (some AST satisfies it)"
    );

    // The public decision entrypoint must agree with the hand computation.
    assert!(
        parity_tree::decide_recursive_predicate(&pred),
        "decide_recursive_predicate(reachable) must report SATISFIABLE (PATA non-empty)"
    );
}

#[test]
fn positive_spin_is_unsatisfiable() {
    let pred = spin_predicate();

    let pata = mettail_prattail::letprop::letprop_to_pata(&pred, pred.params.len().max(1))
        .expect("spin predicate must lower to a PATA");
    assert!(
        pata.num_states() > 0,
        "the `spin` least-fixpoint must still compile to a non-trivial PATA (got 0 states)"
    );

    assert!(
        parity_tree::check_emptiness(&pata),
        "`spin = spin` is a baseless least fixpoint (odd-priority self-loop), so its PATA must be \
         EMPTY (no AST satisfies it)"
    );

    assert!(
        !parity_tree::decide_recursive_predicate(&pred),
        "decide_recursive_predicate(spin) must report UNSATISFIABLE (PATA empty) — the dead \
         behavioral type LP01 flags"
    );
}

/// The two synthetic predicates must land on OPPOSITE verdicts, so the positive
/// gate genuinely exercises both branches of the emptiness decision rather than
/// trivially agreeing.
#[test]
fn synthetic_predicates_have_opposite_verdicts() {
    let sat = parity_tree::decide_recursive_predicate(&reachable_predicate());
    let unsat = parity_tree::decide_recursive_predicate(&spin_predicate());
    assert!(
        sat && !unsat,
        "expected reachable=SAT (true) and spin=UNSAT (false); got reachable={sat}, spin={unsat}"
    );
}
