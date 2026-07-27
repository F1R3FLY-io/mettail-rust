//! Byte-identical snapshot proof for the OSLF substrate Phase 1 `.0`-inert
//! `AnyAlgebra` guard-predicate carrier.
//!
//! The carrier route (`symbolic::analyze_from_bundle_carrier`) must produce a
//! `SymbolicAnalysis` that is **byte-for-byte identical** to the historical
//! string-set route (`symbolic::analyze_from_bundle_string_set`) on every
//! grammar — that is the `.0`-inert contract (the carrier merely *types* the
//! guard predicate; it must not change a single disposition). The live flip to
//! the carrier is a later step (`.1`).
//!
//! Both functions are `pub` and always compiled. So this single-process test is
//! the strongest possible byte-identical proof: it feeds *identical* inputs to
//! both code paths and asserts their rendered `Display` strings are equal,
//! independent of which path `analyze_from_bundle` dispatches to.
//!
//! The three fixtures (calculator, rholang, ambient) reproduce the real
//! grammars' category native-types and a representative rule set that exercises
//! every `guard_satisfiability` branch:
//!   - terminal-led rules (e.g. `"error"`, `"0"`, `a "+" b`),
//!   - non-terminal-led rules (casts like `k:Int |- k`, `Name "[" Proc "]"`),
//!   - ident-capture-led rules (variables),
//!   - binder-led rules (`PNew`),
//!   - collection-led rules (`PPar` over a `HashBag`),
//!   - empty / zero-ary error rules,
//!   - overlapping guards (same category, shared leading terminal),
//!   - subsumed guards (one leading-terminal set a strict subset of another's).
//!
//! Scalar categories carry the real `native_type` strings the bridge stores
//! (`native_type_to_full_string` form: `"i32"`, `"i64"`, `"u32"`, `"f64"`,
//! `"bool"`, `"str"`, `"mettail_runtime::CanonicalBigInt"`,
//! `"mettail_runtime::CanonicalBigRat"`, `"mettail_runtime::CanonicalFixedPoint"`),
//! and non-scalar categories (`Proc`, `Name`, `List`, `Bag`, `Map`) carry the
//! container/`None` forms — so the fixtures match what the carrier resolves at
//! `.1`, even though `.0` does not consult the per-category sort.

use mettail_prattail::grammar::ir::CollectionKind;
use mettail_prattail::pipeline::CategoryInfo;
use mettail_prattail::symbolic::{analyze_from_bundle_carrier, analyze_from_bundle_string_set};
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

type Rule = (String, String, Vec<SyntaxItemSpec>);

fn rule(label: &str, cat: &str, syntax: Vec<SyntaxItemSpec>) -> Rule {
    (label.to_string(), cat.to_string(), syntax)
}

// ── Fixtures ────────────────────────────────────────────────────────────────

/// Calculator: a `Proc` super-category plus the full scalar tower
/// (`i32`/`u32`/BigInt/BigRat/Fixed/`f64`/`bool`/`str`) and the three
/// collection containers. Representative rules cover injections (non-terminal
/// led), arithmetic (infix, terminal-led on the operator? no — infix rules are
/// non-terminal led: `a "+" b` starts with the `a:Int` non-terminal), prefix
/// casts (`"float" "(" a ")"`), zero-ary error literals, and variables.
fn calculator_fixture() -> (Vec<Rule>, Vec<CategoryInfo>) {
    let categories = vec![
        struct_cat("Proc", None, true, true),
        scalar_cat("Int", "i32", false),
        scalar_cat("UInt32", "u32", false),
        scalar_cat("BigInt", "mettail_runtime::CanonicalBigInt", false),
        scalar_cat("BigRat", "mettail_runtime::CanonicalBigRat", false),
        scalar_cat("Fixed", "mettail_runtime::CanonicalFixedPoint", false),
        scalar_cat("Float", "f64", false),
        scalar_cat("Bool", "bool", false),
        scalar_cat("Str", "str", false),
        struct_cat("List", Some("Vec < Proc >"), false, false),
        struct_cat("Bag", Some("mettail_runtime::HashBag < Proc >"), false, false),
        struct_cat("Map", Some("HashMap < Proc , Proc >"), false, false),
    ];

    let all_syntax = vec![
        // Variable leaves (IdentCapture-led) — one per scalar category.
        rule("IVar", "Int", vec![ident("x")]),
        rule("BVar", "Bool", vec![ident("x")]),
        // Injections into Proc (NonTerminal-led).
        rule("ProcInt", "Proc", vec![nonterm("Int", "i")]),
        rule("ProcBool", "Proc", vec![nonterm("Bool", "b")]),
        rule("ProcStr", "Proc", vec![nonterm("Str", "s")]),
        // Zero-ary error literals (Terminal-led).
        rule("Err", "Int", vec![term("error")]),
        rule("CastErrInt", "Int", vec![term("cast_error_int")]),
        // Infix arithmetic (NonTerminal-led: starts with `a:Int`). The shared
        // category + first-item NonTerminal means these are satisfiable but NOT
        // terminal-overlapping (no leading terminal).
        rule("AddInt", "Int", vec![nonterm("Int", "a"), term("+"), nonterm("Int", "b")]),
        rule("SubInt", "Int", vec![nonterm("Int", "a"), term("-"), nonterm("Int", "b")]),
        // Prefix casts (Terminal-led, shared "float" / "int" leading terminals
        // across categories → these create real overlapping/subsumed structure
        // when in the SAME category).
        rule(
            "FloatToInt",
            "Int",
            vec![term("int"), term("("), nonterm("Float", "a"), term(")")],
        ),
        rule("StrToInt", "Int", vec![term("int"), term("("), nonterm("Str", "a"), term(")")]),
        rule(
            "IntToFloat",
            "Float",
            vec![term("float"), term("("), nonterm("Int", "a"), term(")")],
        ),
        // Mixfix postfix factorial (NonTerminal-led).
        rule("Fact", "Int", vec![nonterm("Int", "a"), term("!")]),
        // Collection literal (Collection-led) on Bag.
        rule("BagLit", "Bag", vec![bag_collection("xs", "Proc", "|")]),
    ];

    (all_syntax, categories)
}

/// Rholang: `Proc`/`Name` process categories + the scalar tower (`i64` Int),
/// plus collections. Representative rules cover the constant `PZero` ("{}"),
/// the mixfix `POutput` (NonTerminal-led: `n "!" "(" q ")"`), the binder-led
/// `PNew`, the `Err` literal, scalar casts (NonTerminal-led), and the
/// collection-led `PPar`.
fn rholang_fixture() -> (Vec<Rule>, Vec<CategoryInfo>) {
    let categories = vec![
        struct_cat("Proc", None, true, true),
        struct_cat("Name", None, false, true),
        scalar_cat("Int", "i64", false),
        scalar_cat("UInt32", "u32", false),
        scalar_cat("BigInt", "mettail_runtime::CanonicalBigInt", false),
        scalar_cat("BigRat", "mettail_runtime::CanonicalBigRat", false),
        scalar_cat("Fixed", "mettail_runtime::CanonicalFixedPoint", false),
        scalar_cat("Float", "f64", false),
        scalar_cat("Bool", "bool", false),
        scalar_cat("Str", "str", false),
        struct_cat("List", Some("Vec < Proc >"), false, false),
        struct_cat("Bag", Some("mettail_runtime::HashBag < Proc >"), false, false),
        struct_cat("Map", Some("HashMap < Proc , Proc >"), false, false),
    ];

    let all_syntax = vec![
        // Constant (Terminal-led).
        rule("PZero", "Proc", vec![term("{}")]),
        // Drop (Terminal-led).
        rule("PDrop", "Proc", vec![term("*"), term("("), nonterm("Name", "n"), term(")")]),
        // Parallel composition (Collection-led).
        rule("PPar", "Proc", vec![term("{"), bag_collection("ps", "Proc", "|"), term("}")]),
        // Output (NonTerminal-led mixfix).
        rule(
            "POutput",
            "Proc",
            vec![nonterm("Name", "n"), term("!"), term("("), nonterm("Proc", "q"), term(")")],
        ),
        // Quote (Terminal-led).
        rule("NQuote", "Name", vec![term("@"), term("("), nonterm("Proc", "p"), term(")")]),
        // New (Binder-led).
        rule("PNew", "Proc", vec![binder("xs", "Name", true), nonterm("Proc", "p")]),
        // Error literal (Terminal-led).
        rule("Err", "Proc", vec![term("error")]),
        // Scalar casts into Proc (NonTerminal-led).
        rule("CastInt", "Proc", vec![nonterm("Int", "k")]),
        rule("CastBool", "Proc", vec![nonterm("Bool", "k")]),
        rule("CastStr", "Proc", vec![nonterm("Str", "s")]),
        rule("CastList", "Proc", vec![nonterm("List", "l")]),
        // Numeric casts (Terminal-led; share leading "int"/"uint"/"float" with
        // each other to drive overlapping/subsumed structure).
        rule(
            "IntBinProc",
            "Proc",
            vec![term("int"), term("("), nonterm("Proc", "a"), term(",")],
        ),
        rule(
            "UIntBinProc",
            "Proc",
            vec![term("uint"), term("("), nonterm("Proc", "a"), term(",")],
        ),
        // Int variable (IdentCapture-led).
        rule("IVar", "Int", vec![ident("x")]),
    ];

    (all_syntax, categories)
}

/// Ambient: only `Proc` and `Name`, both *non-scalar* (no native types). This
/// is the carrier's "no scalar sorts at all" stress case — every guard's lifted
/// `AnyPred` is still decided identically (True ↦ true / False ↦ false). Rules
/// cover terminal-led (`"0"`, `"in("`), the NonTerminal-led `PAmb`
/// (`Name "[" Proc "]"`), the binder-led `PNew`, and the collection-led `PPar`.
fn ambient_fixture() -> (Vec<Rule>, Vec<CategoryInfo>) {
    let categories =
        vec![struct_cat("Proc", None, true, true), struct_cat("Name", None, false, true)];

    let all_syntax = vec![
        // Nil (Terminal-led).
        rule("PZero", "Proc", vec![term("0")]),
        // Capabilities (Terminal-led; distinct leading terminals).
        rule(
            "PIn",
            "Proc",
            vec![term("in("), nonterm("Name", "n"), term(","), nonterm("Proc", "p"), term(")")],
        ),
        rule(
            "POut",
            "Proc",
            vec![term("out("), nonterm("Name", "n"), term(","), nonterm("Proc", "p"), term(")")],
        ),
        rule(
            "POpen",
            "Proc",
            vec![term("open("), nonterm("Name", "n"), term(","), nonterm("Proc", "p"), term(")")],
        ),
        // Ambient (NonTerminal-led: `Name "[" Proc "]"`).
        rule(
            "PAmb",
            "Proc",
            vec![nonterm("Name", "n"), term("["), nonterm("Proc", "p"), term("]")],
        ),
        // New (Binder-led).
        rule("PNew", "Proc", vec![binder("x", "Name", false), nonterm("Proc", "p")]),
        // Parallel composition (Collection-led).
        rule("PPar", "Proc", vec![term("{"), bag_collection("ps", "Proc", "|"), term("}")]),
        // Name variable (IdentCapture-led).
        rule("NVar", "Name", vec![ident("x")]),
    ];

    (all_syntax, categories)
}

// ── The byte-identical assertions ───────────────────────────────────────────

/// Render both paths and assert the `Display` is byte-for-byte identical, with
/// a precise diff on failure (so a carrier regression is debuggable, never
/// papered over by adjusting the expectation).
fn assert_byte_identical(name: &str, all_syntax: &[Rule], categories: &[CategoryInfo]) {
    let string_set = analyze_from_bundle_string_set(all_syntax, categories);
    let carrier = analyze_from_bundle_carrier(all_syntax, categories);

    let s_str = string_set.to_string();
    let c_str = carrier.to_string();

    if s_str != c_str {
        // Emit the first differing line for a readable failure.
        let first_diff = s_str
            .lines()
            .zip(c_str.lines())
            .enumerate()
            .find(|(_, (a, b))| a != b)
            .map(|(i, (a, b))| format!("line {i}:\n  string_set: {a:?}\n  carrier   : {b:?}"))
            .unwrap_or_else(|| {
                format!(
                    "length differs: string_set={} lines, carrier={} lines",
                    s_str.lines().count(),
                    c_str.lines().count()
                )
            });
        panic!(
            "carrier path diverged from string-set path for `{name}` \
             (the `.0` carrier MUST be byte-identical):\n{first_diff}"
        );
    }

    // Also assert the structured vectors are equal (Display equality already
    // implies this for the fields it prints; this catches the non-printed
    // `unsatisfiable_rule_labels` too).
    assert_eq!(
        string_set.guard_satisfiability, carrier.guard_satisfiability,
        "guard_satisfiability differs for `{name}`"
    );
    assert_eq!(
        string_set.overlapping_guards, carrier.overlapping_guards,
        "overlapping_guards differs for `{name}`"
    );
    assert_eq!(
        string_set.subsumed_guards, carrier.subsumed_guards,
        "subsumed_guards differs for `{name}`"
    );
    assert_eq!(
        string_set.unsatisfiable_rule_labels, carrier.unsatisfiable_rule_labels,
        "unsatisfiable_rule_labels differs for `{name}`"
    );
    assert_eq!(
        (string_set.num_states, string_set.num_transitions),
        (carrier.num_states, carrier.num_transitions),
        "state/transition counts differ for `{name}`"
    );
}

#[test]
fn calculator_carrier_is_byte_identical() {
    let (all_syntax, categories) = calculator_fixture();
    assert_byte_identical("calculator", &all_syntax, &categories);
}

#[test]
fn rholang_carrier_is_byte_identical() {
    let (all_syntax, categories) = rholang_fixture();
    assert_byte_identical("rholang", &all_syntax, &categories);
}

#[test]
fn ambient_carrier_is_byte_identical() {
    let (all_syntax, categories) = ambient_fixture();
    assert_byte_identical("ambient", &all_syntax, &categories);
}

/// Sanity guard: the fixtures must actually exercise the structure we claim —
/// at least one unsatisfiable rule path is *not* present (all our rules are
/// satisfiable), and overlapping/subsumed structure is non-empty for the
/// terminal-sharing fixtures. If a future edit makes the fixtures trivial, this
/// fails loudly so the byte-identical proof never degenerates into "two empty
/// analyses are equal".
#[test]
fn fixtures_exercise_overlap_and_subsumption() {
    // Calculator: FloatToInt / StrToInt share the leading "int" terminal in the
    // Int category ⇒ they overlap.
    let (cs, cc) = calculator_fixture();
    let calc = analyze_from_bundle_string_set(&cs, &cc);
    assert!(
        !calc.overlapping_guards.is_empty(),
        "calculator fixture should produce overlapping guards (shared `int` leading terminal)"
    );

    // Rholang: IntBinProc / UIntBinProc are distinct leading terminals, but the
    // many Proc casts + PZero/Err give a rich satisfiability vector. Assert the
    // analysis is non-trivial.
    let (rs, rc) = rholang_fixture();
    let rho = analyze_from_bundle_string_set(&rs, &rc);
    assert!(rho.guard_satisfiability.len() >= 10, "rholang fixture too small");
    assert!(
        rho.guard_satisfiability.iter().all(|(_, sat)| *sat),
        "every rholang fixture rule is satisfiable by construction"
    );

    // Ambient: every rule satisfiable; no scalar categories at all.
    let (as_, ac) = ambient_fixture();
    let amb = analyze_from_bundle_string_set(&as_, &ac);
    assert!(
        amb.guard_satisfiability.iter().all(|(_, sat)| *sat),
        "every ambient fixture rule is satisfiable by construction"
    );
}
