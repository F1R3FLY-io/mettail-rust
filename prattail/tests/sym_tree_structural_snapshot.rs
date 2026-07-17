//! Agreement snapshot for the OSLF substrate Phase 2 `.0`-inert structural-type
//! recognizer (`structural_types::structural_verdict`).
//!
//! The `sym_tree`-based recognizer must produce a per-category inhabitation
//! verdict that **agrees category-for-category** with the finite
//! `type_system::SetTheoreticTypeSystem` engine over the *same* ranked alphabet
//! — that is the `.0`-inert contract (the recognizer merely *generalizes* the
//! finite engine to symbolic payloads; over the trivially-satisfiable `True`
//! payload partition it must not change a single emptiness verdict). The live
//! flip — routing structural refinement dispatch through this recognizer and
//! firing RT03 — is `.1`.
//!
//! ## What is compared
//!
//! For each fixture grammar, both engines are built from the **identical** ranked
//! alphabet (rule label = constructor, arity = number of structural children,
//! per `structural_types::collect_structural_child_categories`, which shares its
//! arity logic with `tree_automaton::collect_nonterminal_children`):
//!
//!   - `sym_tree` side: `structural_verdict(...).empty_categories` —
//!     `SymbolicTreeAutomaton<AnyAlgebra>::is_empty` per category, where a
//!     payloaded (scalar) leaf carries the always-satisfiable `True` guard.
//!   - finite side: `SetTheoreticTypeSystem::is_empty` of the per-category
//!     `TreeAutomaton<BooleanWeight>` built directly from the same alphabet (one
//!     state per category, the target category accepting, one `BooleanWeight`-
//!     true transition per rule).
//!
//! Both are bottom-up reachability over the same constructor structure, so they
//! MUST agree. This single-process test feeds identical inputs to both code
//! paths and asserts equal empty-category sets, with a precise diff on failure
//! (so a recognizer regression is debuggable, never papered over by adjusting
//! the expectation). The payloaded/structural split only changes whether a leaf
//! carries a (trivially-satisfiable) `True` guard, which never alters an
//! emptiness verdict.

use std::collections::HashMap;

use mettail_prattail::automata::semiring::{BooleanWeight, Semiring};
use mettail_prattail::pipeline::CategoryInfo;
use mettail_prattail::structural_types::{
    collect_structural_child_categories, ranked_alphabet, structural_verdict, SyntaxRule,
};
use mettail_prattail::tree_automaton::{TreeAutomaton, TreeState, TreeTransition};
use mettail_prattail::type_system::SetTheoreticTypeSystem;
use mettail_prattail::SyntaxItemSpec;

// ── Tiny constructors for readable fixtures ─────────────────────────────────

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
    use mettail_prattail::grammar::ir::CollectionKind;
    SyntaxItemSpec::Collection {
        param_name: name.to_string(),
        element_category: elem_cat.to_string(),
        separator: sep.to_string(),
        kind: CollectionKind::HashBag,
        key_val_separator: None,
    }
}
fn scalar_cat(name: &str, native: &str, is_primary: bool) -> CategoryInfo {
    CategoryInfo {
        name: name.to_string(),
        native_type: Some(native.to_string()),
        is_primary,
        has_var: true,
    }
}
fn struct_cat(name: &str, native: Option<&str>, is_primary: bool, has_var: bool) -> CategoryInfo {
    CategoryInfo {
        name: name.to_string(),
        native_type: native.map(|s| s.to_string()),
        is_primary,
        has_var,
    }
}
fn rule(label: &str, cat: &str, syntax: Vec<SyntaxItemSpec>) -> SyntaxRule {
    (label.to_string(), cat.to_string(), syntax)
}

// ══════════════════════════════════════════════════════════════════════════════
// Finite-engine bridge: build SetTheoreticTypeSystem per-category emptiness over
// the SAME ranked alphabet the sym_tree recognizer uses.
// ══════════════════════════════════════════════════════════════════════════════

/// Build, for each category, the `TreeAutomaton<BooleanWeight>` that accepts that
/// category's terms — one state per category, the target category's state
/// accepting, one true-weighted transition per rule (label = constructor, child
/// states = structural children's categories) — and return the
/// `SetTheoreticTypeSystem`'s `is_empty` verdict per category, as a sorted
/// `Vec<String>` of the empty category names.
///
/// This uses the *same* `collect_structural_child_categories` the sym_tree side
/// uses (so the alphabet is arity-identical) and the *same* category set. The
/// only structural difference vs. the sym_tree automaton is the absence of a
/// (trivially-satisfiable) payload guard on scalar leaves — which is exactly the
/// `.0` invariant under test: it cannot change an emptiness verdict.
fn finite_engine_empty_categories(
    all_syntax: &[SyntaxRule],
    categories: &[CategoryInfo],
) -> Vec<String> {
    // The shared category universe (declared categories + any referenced child /
    // owning categories), matching `RankedAlphabet::categories`.
    let alpha = ranked_alphabet(all_syntax, categories);
    let mut cats: Vec<String> = alpha.categories.iter().cloned().collect();
    cats.sort();

    // Stable per-category state ids (sorted) — identical indexing discipline to
    // `category_automaton`.
    let state_of: HashMap<&str, usize> = cats
        .iter()
        .enumerate()
        .map(|(i, c)| (c.as_str(), i))
        .collect();

    // Constructors with their arities (the SetTheoreticTypeSystem term algebra).
    let constructors: HashMap<String, usize> = alpha.arities.clone();
    let mut system = SetTheoreticTypeSystem::new(constructors);

    // For each category, define a TreeAutomaton accepting that category's terms.
    for target in &cats {
        let mut aut: TreeAutomaton<BooleanWeight> = TreeAutomaton::new();
        // One state per category; mark only the target accepting.
        for c in &cats {
            let is_final = c == target;
            let id = aut.add_state(is_final);
            // States are added in `cats` (sorted) order, so id == state_of[c].
            debug_assert_eq!(id, state_of[c.as_str()]);
            // Label the state for readable diagnostics.
            aut.states[id] = TreeState::labeled(id, c.clone(), is_final);
        }
        // One transition per rule.
        for (label, owning_cat, items) in all_syntax {
            let target_state = match state_of.get(owning_cat.as_str()) {
                Some(&s) => s,
                None => continue,
            };
            let mut child_cats = Vec::new();
            collect_structural_child_categories(items, &mut child_cats);
            // Map child categories → states; skip if any is unknown.
            let mut child_states = Vec::with_capacity(child_cats.len());
            let mut resolvable = true;
            for cc in &child_cats {
                match state_of.get(cc.as_str()) {
                    Some(&s) => child_states.push(s),
                    None => {
                        resolvable = false;
                        break;
                    },
                }
            }
            if !resolvable {
                continue;
            }
            aut.ranked_alphabet
                .entry(label.clone())
                .or_insert(child_states.len());
            aut.add_transition(TreeTransition {
                symbol: label.clone(),
                child_states,
                target_state,
                weight: BooleanWeight::one(),
            });
        }
        system.define_type(target.clone(), aut);
    }

    // Per-category emptiness via the finite engine.
    let mut empty = Vec::new();
    for target in &cats {
        let aut =
            system.type_to_automaton(&mettail_prattail::type_system::SetType::Atom(target.clone()));
        if SetTheoreticTypeSystem::is_empty(&aut) {
            empty.push(target.clone());
        }
    }
    empty.sort();
    empty
}

/// The agreement assertion: the sym_tree recognizer's empty-category set equals
/// the finite engine's, with a precise diff on failure.
fn assert_agrees(name: &str, all_syntax: &[SyntaxRule], categories: &[CategoryInfo]) {
    let mut sym_empty = structural_verdict(all_syntax, categories).empty_categories;
    sym_empty.sort();
    let finite_empty = finite_engine_empty_categories(all_syntax, categories);

    if sym_empty != finite_empty {
        let only_sym: Vec<&String> = sym_empty
            .iter()
            .filter(|c| !finite_empty.contains(c))
            .collect();
        let only_finite: Vec<&String> = finite_empty
            .iter()
            .filter(|c| !sym_empty.contains(c))
            .collect();
        panic!(
            "structural-type recognizer diverged from SetTheoreticTypeSystem for `{name}` \
             (the `.0` recognizer MUST agree category-for-category):\n  \
             sym_tree empty   : {sym_empty:?}\n  \
             finite   empty   : {finite_empty:?}\n  \
             only in sym_tree : {only_sym:?}\n  \
             only in finite   : {only_finite:?}"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Fixtures
// ══════════════════════════════════════════════════════════════════════════════

/// Calculator: a `Proc` super-category, scalar `Int`/`Bool`/`Str`, the three
/// collection containers, and arithmetic / cast / variable rules. Every category
/// is inhabited (no degenerate recursion).
fn calculator_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
    let categories = vec![
        struct_cat("Proc", None, true, true),
        scalar_cat("Int", "i32", false),
        scalar_cat("Bool", "bool", false),
        scalar_cat("Str", "str", false),
        struct_cat("List", Some("Vec < Proc >"), false, false),
        struct_cat("Bag", Some("mettail_runtime::HashBag < Proc >"), false, false),
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

/// RhoCalc: `Proc`/`Name` process categories + scalar `Int`, with the constant
/// `PZero`, the mixfix `POutput`, the binder-led `PNew`, scalar casts, and the
/// collection-led `PPar`. All categories inhabited.
fn rhocalc_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
    let categories = vec![
        struct_cat("Proc", None, true, true),
        struct_cat("Name", None, false, true),
        scalar_cat("Int", "i64", false),
        struct_cat("List", Some("Vec < Proc >"), false, false),
        struct_cat("Bag", Some("mettail_runtime::HashBag < Proc >"), false, false),
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
/// stress case). All categories inhabited (`PZero` / `NVar` base cases).
fn ambient_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
    let categories =
        vec![struct_cat("Proc", None, true, true), struct_cat("Name", None, false, true)];
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

/// `List = Nil | Cons(Int, List)`: a finite-payload recursive ADT with a base
/// case (inhabited) plus a deliberately base-case-less `Expr = App(Expr, Expr)`
/// (empty). This is the discriminating fixture — the engines must AGREE that
/// `List`/`Int` are inhabited and `Expr` is empty.
fn list_and_expr_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
    let categories = vec![
        struct_cat("Proc", None, true, true),
        scalar_cat("Int", "i64", false),
        struct_cat("List", Some("Vec < Int >"), false, false),
        struct_cat("Expr", None, false, true),
    ];
    let all_syntax = vec![
        rule("IVar", "Int", vec![ident("x")]),
        rule("ProcList", "Proc", vec![nonterm("List", "l")]),
        rule("Nil", "List", vec![term("nil")]),
        rule("Cons", "List", vec![nonterm("Int", "h"), nonterm("List", "t")]),
        // Expr has only a recursive rule — no base case ⇒ uninhabited.
        rule("App", "Expr", vec![nonterm("Expr", "f"), nonterm("Expr", "a")]),
    ];
    (all_syntax, categories)
}

/// A symbolic-payload `Expr` *tree* over scalar leaves: `Expr = Lit(Int) |
/// Var(Str) | Bin(Expr, Expr)` plus a base-case-less `Dead = Wrap(Dead)`. `Expr`
/// is inhabited (the `Lit`/`Var` leaves bottom out the recursion), `Dead` is
/// empty.
fn expr_tree_fixture() -> (Vec<SyntaxRule>, Vec<CategoryInfo>) {
    let categories = vec![
        struct_cat("Expr", None, true, true),
        scalar_cat("Int", "i64", false),
        scalar_cat("Str", "str", false),
        struct_cat("Dead", None, false, true),
    ];
    let all_syntax = vec![
        rule("ILit", "Int", vec![term("0")]),
        rule("SLit", "Str", vec![term("\"\"")]),
        rule("Lit", "Expr", vec![nonterm("Int", "n")]),
        rule("Var", "Expr", vec![nonterm("Str", "s")]),
        rule("Bin", "Expr", vec![nonterm("Expr", "l"), term("+"), nonterm("Expr", "r")]),
        // Dead has only a self-recursive rule — uninhabited.
        rule("Wrap", "Dead", vec![term("wrap("), nonterm("Dead", "d"), term(")")]),
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
fn rhocalc_agrees() {
    let (all_syntax, categories) = rhocalc_fixture();
    assert_agrees("rhocalc", &all_syntax, &categories);
}

#[test]
fn ambient_agrees() {
    let (all_syntax, categories) = ambient_fixture();
    assert_agrees("ambient", &all_syntax, &categories);
}

#[test]
fn list_and_expr_agrees() {
    let (all_syntax, categories) = list_and_expr_fixture();
    assert_agrees("list_and_expr", &all_syntax, &categories);
}

#[test]
fn expr_tree_agrees() {
    let (all_syntax, categories) = expr_tree_fixture();
    assert_agrees("expr_tree", &all_syntax, &categories);
}

/// Non-degeneracy guard: the fixtures must actually exercise BOTH an empty and an
/// inhabited category, so the agreement proof never degenerates into "two
/// all-inhabited verdicts trivially match". If a future edit makes the
/// discriminating fixtures trivial, this fails loudly.
#[test]
fn fixtures_exercise_empty_and_inhabited() {
    // list_and_expr: Expr empty, List + Int inhabited.
    let (ls, lc) = list_and_expr_fixture();
    let lv = structural_verdict(&ls, &lc);
    assert!(
        lv.empty_categories.contains(&"Expr".to_string()),
        "list_and_expr must have an EMPTY category (Expr): {:?}",
        lv.empty_categories
    );
    assert!(
        !lv.empty_categories.contains(&"List".to_string())
            && !lv.empty_categories.contains(&"Int".to_string()),
        "list_and_expr must have INHABITED categories (List, Int): {:?}",
        lv.empty_categories
    );
    // And the finite engine must independently agree on the same split (so the
    // non-degeneracy is real on BOTH sides, not just the sym_tree side).
    let finite = finite_engine_empty_categories(&ls, &lc);
    assert!(
        finite.contains(&"Expr".to_string())
            && !finite.contains(&"List".to_string())
            && !finite.contains(&"Int".to_string()),
        "finite engine must independently witness the empty/inhabited split: {finite:?}"
    );

    // expr_tree: Dead empty, Expr + Int + Str inhabited.
    let (es, ec) = expr_tree_fixture();
    let ev = structural_verdict(&es, &ec);
    assert!(
        ev.empty_categories.contains(&"Dead".to_string()),
        "expr_tree must have an EMPTY category (Dead): {:?}",
        ev.empty_categories
    );
    assert!(
        !ev.empty_categories.contains(&"Expr".to_string()),
        "expr_tree Expr must be inhabited: {:?}",
        ev.empty_categories
    );

    // A witness genuinely exists for an inhabited category and is accepted.
    let alpha = ranked_alphabet(&es, &ec);
    let elem = mettail_prattail::structural_types::build_tree_algebra(&alpha);
    let expr_auto = mettail_prattail::structural_types::category_automaton("Expr", &alpha, &elem);
    let w = expr_auto.witness().expect("Expr inhabited ⇒ witness");
    assert!(expr_auto.accepts(&w), "Expr witness must be accepted by its automaton");
}
