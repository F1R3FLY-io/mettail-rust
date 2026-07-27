use mettail_languages::calculator::{self as calc};
use mettail_runtime::Language;

// --- Int: simple and precedence ---

#[test]
fn test_bigint_parse_eval_large_value() {
    mettail_runtime::clear_var_cache();
    let value = calc::BigInt::parse("123456789012345678901234567890n").expect("parse bigint");
    assert_eq!(value.eval().to_string(), "123456789012345678901234567890");
}

#[test]
fn test_bigint_and_i32_are_distinct() {
    mettail_runtime::clear_var_cache();
    let parse_result = calc::Int::parse("1n + 2n");
    assert!(
        parse_result.is_err(),
        "BigInt literals should not parse as Int without explicit cast/coercion"
    );
}

#[test]
fn test_fraction_accepts_bigint_or_int_args() {
    // With the `n`/`r` suffix made optional + Int→BigInt injection widening,
    // `fraction(1, 2)` now parses successfully (bare ints widen to BigInt).
    // Earlier semantics required explicit `n` suffix.
    mettail_runtime::clear_var_cache();
    assert!(calc::BigRat::parse("fraction(1, 2)").is_ok());
    assert!(calc::BigRat::parse("fraction(1n, 2n)").is_ok());
}

// --- Int: division, modulus (%), div/mod by zero ---

// --- Int: literal bounds (i32), optional i32 suffix ---

#[test]
fn test_int_literal_rejects_above_i32_max() {
    mettail_runtime::clear_var_cache();
    assert!(calc::Int::parse("2147483648").is_err());
    assert!(calc::Int::parse("2147483648i32").is_err());
}

// --- UInt32: literals and AddUInt32 ---

#[test]
fn test_uint32_parse_rejects_overflow_literal() {
    mettail_runtime::clear_var_cache();
    assert!(calc::UInt32::parse("4294967296u32").is_err());
}

#[test]
fn test_int_parse_rejects_u32_suffix() {
    mettail_runtime::clear_var_cache();
    assert!(calc::Int::parse("1u32").is_err());
}

// --- Int / UInt32: overflow (release wraps; debug uses checked ops and may panic — not asserted in tests) ---

// --- Int: PowInt edge cases ---

// --- Int: corner ---

// --- Float: simple and corner ---

// --- Fixed-point: literals, folds, comparisons, projections ---

#[test]
fn test_fixed_parse_rejects_malformed() {
    mettail_runtime::clear_var_cache();
    assert!(calc::Fixed::parse("10px").is_err());
    assert!(calc::Fixed::parse("1.23p1").is_err());
    assert!(calc::Float::parse("").is_err());
}

// --- Bool ---

// --- Str ---

// --- Environment ---

#[test]
fn test_env_add_and_list() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    let term = lang.parse_term_for_env("7").expect("parse 7");
    lang.add_to_env(env.as_mut(), "x", term.as_ref())
        .expect("add x");
    let bindings = lang.list_env(env.as_ref());
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].0, "x");
    assert_eq!(bindings[0].1, "7");
}

#[test]
fn test_env_remove_and_clear() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    let t1 = lang.parse_term_for_env("1").expect("parse");
    let t2 = lang.parse_term_for_env("2").expect("parse");
    lang.add_to_env(env.as_mut(), "a", t1.as_ref())
        .expect("add a");
    lang.add_to_env(env.as_mut(), "b", t2.as_ref())
        .expect("add b");
    assert_eq!(lang.list_env(env.as_ref()).len(), 2);
    lang.remove_from_env(env.as_mut(), "a").expect("remove a");
    assert_eq!(lang.list_env(env.as_ref()).len(), 1);
    lang.clear_env(env.as_mut());
    assert!(lang.is_env_empty(env.as_ref()));
}

// --- Float literal parsing ---

/// Float support: parse float literal and check canonical wrapper (Eq/Hash/Ord via CanonicalFloat64).
#[test]
fn test_float_literal_parse() {
    mettail_runtime::clear_var_cache();
    let term = calc::Float::parse("1.5").expect("parse 1.5");
    if let calc::Float::FloatLit(v) = term {
        assert!((v.get() - 1.5).abs() < 1e-10);
    } else {
        panic!("expected FloatLit, got {:?}", term);
    }
}

/// REPL-style: "1.0" parses as Float (parser order Float-before-Int) via full language parse.
#[test]
fn test_exec_float_1_0() {
    mettail_runtime::clear_var_cache();
    let term = calc::CalculatorLanguage::parse("1.0").expect("parse 1.0");
    let ok = match &term.0 {
        calc::CalculatorTermInner::Float(inner) => matches!(inner, calc::Float::FloatLit(v) if (v.get() - 1.0).abs() < 1e-10),
        calc::CalculatorTermInner::Ambiguous(alts) => alts.iter().any(|a| match a {
            calc::CalculatorTermInner::Float(inner) => matches!(inner, calc::Float::FloatLit(v) if (v.get() - 1.0).abs() < 1e-10),
            calc::CalculatorTermInner::Proc(p) => matches!(p, calc::Proc::ProcFloat(inner) if matches!(inner.as_ref(), calc::Float::FloatLit(v) if (v.get() - 1.0).abs() < 1e-10)),
            _ => false,
        }),
        _ => false,
    };
    assert!(ok, "expected Float or Ambiguous containing Float(1.0), got {:?}", term.0);
}

// --- PraTTaIL-specific: unary prefix, right-assoc, postfix, ternary ---

use mettail_languages::calculator::Int;

#[test]
fn test_unary_minus_literal() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-3").expect("should parse -3");
    assert_eq!(result.eval(), -3);
}

#[test]
fn test_unary_minus_with_addition() {
    mettail_runtime::clear_var_cache();
    // Should parse as (-3) + 5 = 2, NOT -(3 + 5) = -8
    let result = Int::parse("-3 + 5").expect("should parse -3 + 5");
    assert_eq!(result.eval(), 2, "unary minus should bind tighter than addition");
}

#[test]
fn test_unary_minus_with_subtraction() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-3 - 5").expect("should parse -3 - 5");
    assert_eq!(result.eval(), -8, "unary minus should bind tighter than subtraction");
}

#[test]
fn test_binary_minus_with_unary() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("3 - -5").expect("should parse 3 - -5");
    assert_eq!(result.eval(), 8, "binary minus then unary minus in prefix position");
}

#[test]
fn test_double_negation() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("--3").expect("should parse --3");
    assert_eq!(result.eval(), 3, "double negation should cancel out");
}

#[test]
fn test_unary_minus_with_exponentiation() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-3 ^ 2").expect("should parse -3 ^ 2");
    assert_eq!(result.eval(), 9, "unary minus should bind tighter than exponentiation");
}

#[test]
fn test_unary_minus_variable() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-x");
    assert!(result.is_ok(), "should parse -x as Neg(IVar(x))");
}

#[test]
fn test_not_binds_tight() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();
    let result = Bool::parse("not true and false").expect("should parse not true and false");
    assert_eq!(result.eval(), false, "not should bind tighter than and");
}

// ── Right-associativity tests ──

#[test]
fn test_pow_right_associativity() {
    mettail_runtime::clear_var_cache();
    // 2 ^ 3 ^ 2 should parse as 2 ^ (3 ^ 2) = 2 ^ 9 = 512
    let result = Int::parse("2 ^ 3 ^ 2").expect("should parse");
    assert_eq!(result.eval(), 512, "^ should be right-associative");
}

#[test]
fn test_pow_right_assoc_cast_error_chain_parses() {
    mettail_runtime::clear_var_cache();
    Int::parse(
        "cast_error_int ^ cast_error_int ^ cast_error_int ^ cast_error_int ^ \
         cast_error_int ^ cast_error_int ^ cast_error_int ^ cast_error_int",
    )
    .expect("right-associative power chain with keyword operands should parse");
}

#[test]
fn test_pow_simple() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("2 ^ 10").expect("should parse");
    assert_eq!(result.eval(), 1024, "2 ^ 10 = 1024");
}

// ── Postfix operator tests ──

#[test]
fn test_factorial_simple() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("5!").expect("should parse 5!");
    assert_eq!(result.eval(), 120, "5! = 120");
}

#[test]
fn test_factorial_zero() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("0!").expect("should parse 0!");
    assert_eq!(result.eval(), 1, "0! = 1");
}

#[test]
fn test_factorial_with_addition() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("3 + 5!").expect("should parse 3 + 5!");
    assert_eq!(result.eval(), 123, "postfix ! should bind tighter than +");
}

/// ★ RE-DERIVED 2026-07-27 (ledger D1, `languages/tests/literal_domain_agreement.rs`).
///
/// This test was written under "merge decision #4" — the calculator `Int` regex dropped
/// its leading `-?` on the ground that Rholang treats unary minus as an operator rather
/// than a signed literal — and asserted the CONSEQUENCE of that: `-3!` no longer forks in
/// the lex DAG, so the atomic-negative branch `Fact(NumLit(-3))` must not appear.
///
/// The premise was refuted (Rholang's own grammar puts the sign INSIDE the token:
/// `long_literal /-?\d+/`), and it left `i32::MIN` with no surface at all — its `Display`
/// is `-2147483648` and the operator form does not exist for it, since `Neg`'s operand
/// `2147483648` overflows `i32`. `Int`'s pattern carries `-?` again, so the fork is back.
///
/// The test therefore asserts the opposite of its old negative clause, and that is the
/// point rather than a concession: `-3!` is genuinely ambiguous between the two readings
/// below, they DENOTE THE SAME NUMBER, and never-disambiguate-early says an ambiguity
/// belongs in the lattice rather than being removed by narrowing the lexer.
///
///   * `-(3!) = Neg(Fact(NumLit(3)))`   — postfix `!` binds tighter than prefix `-`
///   * `(-3)! = Fact(NumLit(-3))`       — the sign is part of the numeral token
///
/// The operator-spelled inner negative `Fact(Neg(NumLit(3)))` is NOT among them: with a
/// signed literal available, `-3` is spelled atomically, so the `(-3)!` reading carries
/// its sign in the literal. That is one reading of `(-3)!`, not two.
#[test]
fn calculator_unary_minus_factorial_parser_exposes_both_alternatives() {
    use calc::Int;

    mettail_runtime::clear_var_cache();
    let alts = Int::parse_via_wpda_all("-3!").expect("-3! should parse through WPDA");

    // Operator-form reading: -(3!) = Neg(Fact(NumLit(3))).
    assert!(
        alts.iter().any(|t| {
            matches!(
                t,
                Int::Neg(a)
                    if matches!(a.as_ref(), Int::Fact(b) if matches!(b.as_ref(), Int::NumLit(3)))
            )
        }),
        "expected operator-form reading Neg(Fact(NumLit(3))); got {:?}",
        alts
    );
    // Atomic-negative reading: (-3)! = Fact(NumLit(-3)).
    assert!(
        alts.iter()
            .any(|t| matches!(t, Int::Fact(a) if matches!(a.as_ref(), Int::NumLit(-3)))),
        "expected atomic-negative reading Fact(NumLit(-3)) — the `Int` literal is signed \
         again (D1), so the lex DAG forks at a sign-abutted numeral; got {:?}",
        alts
    );
}

/// Calculator-map cross-cat fan-out fix (§6.3 / S7) — gate-disjointness
/// regression for the single-result weight-dominance subsumption.
///
/// The subsumption pass (`subsume_weight_dominated_when_single_result`,
/// `docs/design/calculator-map-crosscat-fanout.md` §4) fires ONLY on the
/// single-result demand path. The multi-result `_all` facade
/// (`parse_via_wpda_all`) routes through the NON-demand driver, so the demand
/// flag is never set and the pass is a no-op there.
///
/// ★ RE-DERIVED 2026-07-27 (ledger D1). This test's SUBJECT is gate disjointness — the
/// single-result subsumption pass must be a no-op on the multi-result `_all` path — and
/// `-3!` is only its vehicle. Under "merge decision #4" the vehicle had become degenerate:
/// with a signless `Int` literal `-3!` had ONE Int-category reading, so "ambiguity is
/// preserved by the `_all` facade" was being asserted over a term with no ambiguity left
/// to preserve, and the test would have passed even if subsumption had collapsed the path.
///
/// D1 restored the sign to the `Int` literal, so `-3!` is two-way ambiguous again and the
/// vehicle carries the subject once more: BOTH readings must survive with
/// `PRATTAIL_SR_SUBSUME` at its production default.
#[test]
fn all_facade_preserves_ambiguity_with_sr_subsume_default_on() {
    use calc::Int;

    // Default environment ⇒ PRATTAIL_SR_SUBSUME is On (the production default).
    mettail_runtime::clear_var_cache();
    let alts = Int::parse_via_wpda_all("-3!").expect("-3! should parse through WPDA");

    // Operator-form reading must survive on the _all path with single-result
    // subsumption default-ON (gate disjointness, S7).
    assert!(
        alts.iter().any(|t| {
            matches!(
                t,
                Int::Neg(a)
                    if matches!(a.as_ref(), Int::Fact(b) if matches!(b.as_ref(), Int::NumLit(3)))
            )
        }),
        "operator-form reading Neg(Fact(NumLit(3))) must survive on the _all path \
         with single-result subsumption default-ON; got {:?}",
        alts
    );
    // …and so must the atomic-negative reading: subsumption is single-result-only, so the
    // `_all` path must not drop EITHER member of a genuine ambiguity.
    assert!(
        alts.iter()
            .any(|t| matches!(t, Int::Fact(a) if matches!(a.as_ref(), Int::NumLit(-3)))),
        "atomic-negative reading Fact(NumLit(-3)) must ALSO survive on the _all path — \
         the subsumption gate is disjoint from the multi-result driver; got {:?}",
        alts
    );
}

/// ★ RE-DERIVED 2026-07-27 (ledger D1). The SUBJECT is prefix agreement: the
/// bounded-demand parser (`parse_via_wpda_prefix_with_weights`) must return the same
/// eager prefix (terms + weights) as the unbounded `_all` parser at every demand.
///
/// Under "merge decision #4" `-3!` had a single Int-category reading, which made the
/// `prefix(2)` leg below identical to the `prefix(1)` leg and the whole agreement claim
/// vacuous past demand 1. D1 restored the signed `Int` literal, so `-3!` has TWO readings
/// and each demand level now discriminates: this asserts the count that makes the legs
/// meaningful, not merely the count that happens to hold.
#[test]
fn calculator_wpda_prefix_matches_eager_prefix_for_unary_minus_factorial() {
    use calc::Int;

    mettail_runtime::clear_var_cache();
    let (eager_terms, eager_weights) =
        Int::parse_via_wpda_all_with_weights("-3!").expect("-3! should parse through WPDA");
    assert_eq!(
        eager_terms.len(),
        2,
        "-3! is two-way ambiguous at Int — `Fact(NumLit(-3))` and `Neg(Fact(NumLit(3)))`; \
         got {:?}",
        eager_terms
    );
    assert_eq!(eager_terms.len(), eager_weights.len());

    let (zero_terms, zero_weights) =
        Int::parse_via_wpda_prefix_with_weights("-3!", 0).expect("zero-demand prefix parses");
    assert!(zero_terms.is_empty());
    assert!(zero_weights.is_empty());

    let (prefix_one, prefix_one_weights) =
        Int::parse_via_wpda_prefix_with_weights("-3!", 1).expect("prefix(1) parses");
    assert_eq!(prefix_one, eager_terms.iter().take(1).cloned().collect::<Vec<_>>());
    assert_eq!(prefix_one_weights, eager_weights.iter().take(1).cloned().collect::<Vec<_>>());

    let (prefix_two, prefix_two_weights) =
        Int::parse_via_wpda_prefix_with_weights("-3!", 2).expect("prefix(2) parses");
    assert_eq!(prefix_two, eager_terms.iter().take(2).cloned().collect::<Vec<_>>());
    assert_eq!(prefix_two_weights, eager_weights.iter().take(2).cloned().collect::<Vec<_>>());
}

/// ★ RE-DERIVED 2026-07-27 (ledger D1 in `languages/tests/literal_domain_agreement.rs`),
/// and the THIRD assertion is the one that moved.
///
/// At the LANGUAGE level `-3!` is genuinely ambiguous, and the two readings this test has
/// always guarded are unchanged:
///
///   * `-(3!) = Neg(Fact(NumLit(3)))`  — postfix `!` binds tighter than prefix `-`
///   * `(-3)! = Fact(Neg(NumLit(3)))`  — prefix `-` binds tighter
///
/// Under "merge decision #4" the calculator `Int` regex had no leading `-?`, so `-3` had
/// only an operator spelling and the test could add "…and the atomic-negative literal
/// `NumLit(-3)` must NOT appear". D1 restored the `-?` — the decision's premise was refuted
/// by Rholang's own grammar, and its absence left `i32::MIN` with no surface at all — so
/// `-3` now ALSO has a literal spelling and the third reading `(-3)! = Fact(NumLit(-3))` is
/// back. It is denotationally identical to `Fact(Neg(NumLit(3)))` beside it; the negative
/// clause is therefore inverted rather than dropped, so the reading is asserted PRESENT
/// instead of merely being un-forbidden.
///
/// The alternatives are matched on their derived `Debug` (AST) representation —
/// not their `Display` (surface) form — because the `(-3)!` readings only appear
/// wrapped in cross-category injections (`ProcInt(..)`, `IntToBigInt(..)`,
/// `IntToBigRat(..)`), so a substring check over the AST Debug is the robust
/// shape assertion across every wrapper.
#[test]
fn test_factorial_ambiguous_language_parse_preserves_both_alternatives() {
    use calc::CalculatorTermInner;

    mettail_runtime::clear_var_cache();
    let term = calc::CalculatorLanguage::parse("-3!").expect("-3! should parse as language term");
    let alts = match &term.0 {
        CalculatorTermInner::Ambiguous(alts) => alts,
        other => panic!("expected Ambiguous language term for -3!, got {:?}", other),
    };

    // Derived-Debug (AST) of each alternative.
    let asts: Vec<String> = alts.iter().map(|alt| format!("{:?}", alt)).collect();

    // Operator-form reading -(3!) = Neg(Fact(NumLit(3))).
    assert!(
        asts.iter().any(|a| a.contains("Neg(Fact(NumLit(3)))")),
        "expected operator-form reading Neg(Fact(NumLit(3))); got {:?}",
        asts
    );
    // Operator-form reading (-3)! = Fact(Neg(NumLit(3))).
    assert!(
        asts.iter().any(|a| a.contains("Fact(Neg(NumLit(3)))")),
        "expected operator-form reading Fact(Neg(NumLit(3))); got {:?}",
        asts
    );
    // Atomic-negative reading (-3)! = Fact(NumLit(-3)) — the `Int` literal is signed
    // again (D1), so `-3` has a literal spelling as well as an operator one.
    assert!(
        asts.iter().any(|a| a.contains("Fact(NumLit(-3))")),
        "expected atomic-negative reading Fact(NumLit(-3)); got {:?}",
        asts
    );
}

#[test]
fn test_factorial_with_parentheses() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("(3 + 2)!").expect("should parse (3 + 2)!");
    assert_eq!(result.eval(), 120, "(3 + 2)! = 5! = 120");
}

#[test]
fn test_factorial_precedence_over_pow() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("3! ^ 2").expect("should parse 3! ^ 2");
    assert_eq!(result.eval(), 36, "3! ^ 2 = 6^2 = 36");
}

// ── Mixfix operator tests (ternary) ──

#[test]
fn test_ternary_true_branch() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("1 ? 42 : 0").expect("should parse ternary");
    assert_eq!(result.eval(), 42, "nonzero condition selects then-branch");
}

#[test]
fn test_ternary_false_branch() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("0 ? 42 : 99").expect("should parse ternary");
    assert_eq!(result.eval(), 99, "zero condition selects else-branch");
}

#[test]
fn test_ternary_negative_condition() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("-1 ? 10 : 20").expect("should parse ternary with negative condition");
    assert_eq!(result.eval(), 10, "negative nonzero condition selects then-branch");
}

#[test]
fn test_ternary_with_expressions() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("(1 + 0) ? (3 + 4) : (10 - 5)").expect("should parse");
    assert_eq!(result.eval(), 7, "ternary with subexpressions");
}

#[test]
fn test_ternary_right_associativity() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("1 ? 2 : 1 ? 3 : 4").expect("should parse nested ternary");
    assert_eq!(result.eval(), 2, "first condition is nonzero, selects 2");
}

#[test]
fn test_ternary_nested_else() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("0 ? 2 : 1 ? 3 : 4").expect("should parse nested ternary else");
    assert_eq!(result.eval(), 3, "fall through to nested ternary");
}

#[test]
fn test_ternary_lowest_precedence() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("1 + 0 ? 3 + 4 : 5").expect("should parse");
    assert_eq!(result.eval(), 7, "ternary has lower precedence than +");
}

#[test]
fn test_ternary_display_roundtrip() {
    mettail_runtime::clear_var_cache();
    let term = Int::parse("1 ? 2 : 3").expect("should parse");
    let displayed = format!("{}", term);
    mettail_runtime::clear_var_cache();
    let reparsed = Int::parse(&displayed).expect("should reparse displayed ternary");
    assert_eq!(term, reparsed, "display roundtrip should preserve structure");
}

// ── NFA-style multi-category parse (Ambiguous) tests ──

#[test]
fn test_env_substitute_preserves_unchanged_ambiguous_sibling() {
    use calc::{CalculatorTerm, CalculatorTermInner, Int};

    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let mut env = lang.create_env();
    let binding = CalculatorTerm(CalculatorTermInner::Int(Int::NumLit(1)));
    lang.add_to_env(env.as_mut(), "x", &binding).expect("add x");

    let x = mettail_runtime::OrdVar(mettail_runtime::Var::Free(
        mettail_runtime::get_or_create_var("x"),
    ));
    let term = CalculatorTerm(CalculatorTermInner::Ambiguous(vec![
        CalculatorTermInner::Int(Int::IVar(x)),
        CalculatorTermInner::Int(Int::NumLit(7)),
    ]));

    let substituted = lang
        .substitute_env(&term, env.as_ref())
        .expect("substitute_env");
    let substituted = substituted
        .as_any()
        .downcast_ref::<CalculatorTerm>()
        .expect("CalculatorTerm");
    let alts = match &substituted.0 {
        CalculatorTermInner::Ambiguous(alts) => alts,
        other => panic!("expected Ambiguous after substitution, got {:?}", other),
    };

    let has_one = alts
        .iter()
        .any(|alt| matches!(alt, CalculatorTermInner::Int(Int::NumLit(1))));
    let has_seven = alts
        .iter()
        .any(|alt| matches!(alt, CalculatorTermInner::Int(Int::NumLit(7))));
    assert!(
        has_one && has_seven,
        "substitution must preserve changed and unchanged semantic siblings, got {:?}",
        alts
    );
}

#[test]
fn test_ambiguous_parse_variable_expr() {
    // "a + b" should parse successfully (ambiguous across Float/Int).
    mettail_runtime::clear_var_cache();
    let result = calc::CalculatorLanguage::parse("a + b");
    assert!(result.is_ok(), "ambiguous expression should parse: {:?}", result);
    // Display should show the expression regardless of internal ambiguity
    assert_eq!(format!("{}", result.expect("already checked")), "a + b");
}

#[test]
fn test_unambiguous_int_literal() {
    // "42" parses as Int or Ambiguous(ProcInt(Int), Int). Either way we can get value 42.
    mettail_runtime::clear_var_cache();
    let result = calc::CalculatorLanguage::parse("42").expect("parse 42");
    let ok = match &result.0 {
        calc::CalculatorTermInner::Int(inner) => inner.eval() == 42,
        calc::CalculatorTermInner::Ambiguous(alts) => alts.iter().any(|a| match a {
            calc::CalculatorTermInner::Int(inner) => inner.eval() == 42,
            calc::CalculatorTermInner::Proc(p) => {
                matches!(p, calc::Proc::ProcInt(inner) if inner.eval() == 42)
            },
            _ => false,
        }),
        _ => false,
    };
    assert!(ok, "expected Int or Ambiguous containing Int(42) for '42', got {:?}", result.0);
}

#[test]
fn test_unambiguous_float_literal() {
    // "1.5" parses as Float or Ambiguous(ProcFloat(Float), Float). Either way we have Float.
    mettail_runtime::clear_var_cache();
    let result = calc::CalculatorLanguage::parse("1.5").expect("parse 1.5");
    let has_float = match &result.0 {
        calc::CalculatorTermInner::Float(_) => true,
        calc::CalculatorTermInner::Ambiguous(alts) => alts.iter().any(|a| match a {
            calc::CalculatorTermInner::Float(_) => true,
            calc::CalculatorTermInner::Proc(p) => matches!(p, calc::Proc::ProcFloat(_)),
            _ => false,
        }),
        _ => false,
    };
    assert!(
        has_float,
        "expected Float or Ambiguous containing Float for '1.5', got {:?}",
        result.0
    );
}

/// `infer_var_types` should find variable `x` in `x + 1` for multi-type Calculator
/// (regression guard: multi-type languages must not return an empty Vec).
#[test]
fn test_calculator_infer_var_types() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term("x + 1").expect("parse x + 1");
    let var_types = lang.infer_var_types(term.as_ref());
    let x_info = var_types.iter().find(|v| v.name == "x");
    assert!(x_info.is_some(), "x should be found in var types, got: {:?}", var_types);
}

/// `infer_var_type` should find variable `x` by name for multi-type Calculator
/// (regression guard: multi-type languages must not return None).
#[test]
fn test_calculator_infer_var_type() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term("x + 1").expect("parse x + 1");
    let x_type = lang.infer_var_type(term.as_ref(), "x");
    assert!(x_type.is_some(), "x should have inferred type");
}

// ── Bug 2: All comparison operators (not just ==) ──

// ── Bug 1: Parenthesized cross-category expressions ──

// ── Bug 1+2 combined: parenthesized non-equality comparisons ──

// ── REPL-style exec scenario ──

/// Bare variable `a` in Calculator should infer as the primary category.
/// Calculator's primary category is Proc (first in the types list), so all parsers
/// are tried unconditionally. The Ambiguous result gets the primary category preference
/// from `infer_term_type`.
#[test]
fn test_bare_variable_type_is_primary() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let term = lang.parse_term("a").expect("parse 'a'");
    let term_type = lang.infer_term_type(term.as_ref());
    // Calculator's primary category is Proc (first in the types list);
    // "a" is Ambiguous across all categories, type shows primary (Proc)
    assert_eq!(format!("{}", term_type), "Proc");
}

// --- Nested cast expressions (NFA disambiguation) ---

#[test]
fn calculator_cast_then_compare_budget_parity_across_ep_p1_modes() {
    // EP-P1 v3.1 R7-10 (red-team Round 7; ledger §P1): the mid-park
    // budget gate. Under PRATTAIL_EP_P1=on, parked members leave the
    // frontier (uncounted while parked) — this test pins the OBSERVED
    // contract on the cast-then-compare class so any budget-semantics
    // drift between OFF and ON fails the two-state battery: the
    // explicit-budget overflow fires at the lex fan (position 1,
    // BEFORE any parking engages), so both modes report the IDENTICAL
    // overflow at small k and the identical single parse at viable k
    // (probe-verified byte-identical at k ∈ {1, 4, 16, 64}).
    use mettail_prattail::wpda_runtime::{CursorBoundingMode, LatticeTokenSource, WpdaTokenSource};

    let input = "int(float(int(3.14))) == 3";

    // A1 (task #18): the PURE engine — the SOLE engine after #19b physically
    // removed the classic lever (2026-07-15) — counts DISTINCT REALIZED TERMS at
    // resolve, and this cast tower's ~110 structural derivations reconverge to
    // ONE reading (pinned by the k=16 arm below), so 1 <= 4 => Ok. (This k=4 arm
    // doubles as the cross-packing-DUP no-false-fire gate: raw terms.len() would
    // be ~110 > 4, but the DEDUPED count is 1.)
    let dag = calc::lex_dag(input).expect("calculator lex DAG should accept cast-then-compare");
    let source = LatticeTokenSource::new(dag);
    let mut bounded_pos = 0usize;
    let k4 = calc::parse_Bool_via_wpda_all_with_source_and_bounding_mode(
        &source,
        &mut bounded_pos,
        0,
        CursorBoundingMode::AmbiguityBudget(4),
    );
    let (terms, weights) = k4.expect("pure engine: 1 distinct reading <= 4 => Ok");
    assert_eq!(terms.len(), 1, "the cast tower reconverges to one reading");
    assert_eq!(terms.len(), weights.len());

    // Viable k: exactly one parse, EOI reached, in every EP-P1 mode.
    let dag = calc::lex_dag(input).expect("lex");
    let source = LatticeTokenSource::new(dag);
    let mut pos = 0usize;
    let (terms, weights) = calc::parse_Bool_via_wpda_all_with_source_and_bounding_mode(
        &source,
        &mut pos,
        0,
        CursorBoundingMode::AmbiguityBudget(16),
    )
    .expect("k=16 must parse in every EP-P1 mode");
    assert_eq!(pos, source.eof_node());
    assert_eq!(terms.len(), 1, "one surviving parse in every EP-P1 mode");
    assert_eq!(terms.len(), weights.len());
}

#[test]
fn calculator_cast_explicit_budget_reports_overflow_without_default_cap() {
    use mettail_prattail::wpda_runtime::{CursorBoundingMode, LatticeTokenSource, WpdaTokenSource};

    let input = "float(float(10, 64), 64)";
    let dag = calc::lex_dag(input).expect("calculator lex DAG should accept nested float cast");
    let source = LatticeTokenSource::new(dag);

    let mut default_pos = 0usize;
    let (terms, weights) = calc::parse_Float_via_wpda_all_with_source(&source, &mut default_pos, 0)
        .expect("default parser must preserve ambiguity without an implicit budget cap");
    assert_eq!(default_pos, source.eof_node());
    assert_eq!(terms.len(), weights.len());
    assert!(
        !terms.is_empty(),
        "default unbounded results should include at least one nested cast parse"
    );

    // A1 (task #18): `float(float(10, 64), 64)` has exactly ONE DISTINCT reading
    // (deduped), so the PURE engine — the SOLE engine after #19b physically
    // removed the classic lever (2026-07-15) — returns Ok at budget=1 (1 <= 1).
    // The genuine-overflow witness for the pure engine is the rhocalc
    // `@((a)!(0))!()` pin in `rd_a1_budget.rs` (2 distinct readings, fires at N=1).
    let mut bounded_pos = 0usize;
    let all_b1 = calc::parse_Float_via_wpda_all_with_source_and_bounding_mode(
        &source,
        &mut bounded_pos,
        0,
        CursorBoundingMode::AmbiguityBudget(1),
    );
    let (terms, weights) = all_b1.expect("pure engine: 1 distinct reading <= budget 1 => Ok");
    assert_eq!(terms.len(), 1, "one distinct reading for the nested float cast");
    assert_eq!(terms.len(), weights.len());

    let mut prefix_pos = 0usize;
    let prefix_b1 = calc::parse_Float_via_wpda_prefix_with_source_and_bounding_mode(
        &source,
        &mut prefix_pos,
        0,
        1,
        CursorBoundingMode::AmbiguityBudget(1),
    );
    let (terms, _weights) =
        prefix_b1.expect("pure engine: prefix 1 distinct reading <= budget 1 => Ok");
    assert_eq!(terms.len(), 1, "one distinct prefix reading for the nested float cast");
}

#[test]
fn cast_normalization_budget_preserves_in_bound_alternatives() {
    let lang = calc::CalculatorLanguage;
    let metadata = lang.metadata();
    let rewrites = metadata.rewrites();
    for name in ["NormCastUInt32ToBigRatInProc"] {
        let rw = rewrites
            .iter()
            .find(|rw| rw.name == Some(name))
            .unwrap_or_else(|| panic!("missing generated rewrite {name}"));
        assert!(rw.is_guarded, "{name} must expose SyntheticInjGuard as guarded metadata");
        assert!(
            rw.conditions
                .iter()
                .any(|condition| condition.starts_with("synthetic_inj_guard(")),
            "{name} must retain synthetic guard evidence in metadata: {:?}",
            rw.conditions
        );
    }

    for name in ["NormCastBoolToUInt32InProc", "NormCastFloatToBigRatInProc"] {
        let rw = rewrites
            .iter()
            .find(|rw| rw.name == Some(name))
            .unwrap_or_else(|| panic!("missing generated rewrite {name}"));
        assert!(
            !rw.lhs.is_empty() && !rw.rhs.is_empty(),
            "{name} must remain present as generated cast-normalization evidence"
        );
    }
}

// ── ProcTo* projections from list elements ──

// --- Map ---

#[test]
fn test_map_literal_roundtrip() {
    mettail_runtime::clear_var_cache();
    let term = calc::Map::parse(r#"map(1:"hi", 2:"world")"#).expect("parse map literal");
    let displayed = format!("{}", term);
    mettail_runtime::clear_var_cache();
    let reparsed = calc::Map::parse(&displayed).expect("reparse displayed map");
    assert_eq!(term, reparsed, "map literal display should roundtrip");
}

#[test]
fn test_map_empty_literal_roundtrip() {
    mettail_runtime::clear_var_cache();
    let term = calc::Map::parse("map()").expect("parse empty map");
    let displayed = format!("{}", term);
    mettail_runtime::clear_var_cache();
    let reparsed = calc::Map::parse(&displayed).expect("reparse displayed empty map");
    assert_eq!(term, reparsed);
}

// ── Explicit numeric casts — see `docs/design/made/native-types/numeric-casting.md`

// ── Regression: casts through Proc still work ──

// ── NFA disambiguation: nested casts (duplicate-token prefix arms) ──

// ── NFA spillover + forced-prefix replay disambiguation tests ──

// ── Bug B: Ambiguous dispatch must try ALL operators, not just first ──
//
// When a FIRST token (e.g. Ident) is ambiguous between the target category
// (Bool) and multiple source categories (Int, Float, Str, Bool), ALL
// cross-category operators sharing that FIRST token must be tried. Previously
// only the first operator (by WFST weight) was emitted, so `x >= 1` failed
// while `x == 1` worked.

/// Variable-operand comparisons: Ident tokens hit the ambiguous dispatch path.
/// These test that ALL comparison operators are tried (not just ==).
#[test]
fn test_ambiguous_dispatch_gteq_int() {
    // x >= 1 was the motivating failure — must parse via GtEqInt
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x >= 1");
    assert!(result.is_ok(), "x >= 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_gt_int() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x > 1");
    assert!(result.is_ok(), "x > 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_lt_int() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x < 1");
    assert!(result.is_ok(), "x < 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_lteq_int() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x <= 1");
    assert!(result.is_ok(), "x <= 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_ne_int() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x != 1");
    assert!(result.is_ok(), "x != 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_eq_int_regression() {
    // x == 1 should still work (regression check — was working before)
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x == 1");
    assert!(result.is_ok(), "x == 1 should parse: {:?}", result);
}

#[test]
fn test_ambiguous_dispatch_eq_ident_both_sides() {
    // Both sides are Ident (ambiguous)
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("x == y");
    assert!(result.is_ok(), "x == y should parse: {:?}", result);
}

/// Parenthesized variable comparisons go through the LParen grouping path
/// which re-enters the dispatch.
#[test]
fn test_ambiguous_dispatch_paren_gteq() {
    mettail_runtime::clear_var_cache();
    let lang = calc::CalculatorLanguage;
    let result = lang.parse_term("(x >= 1)");
    assert!(result.is_ok(), "(x >= 1) should parse: {:?}", result);
}

// --- BCG05 regression test ---

#[test]
fn debug_cross_category_cast() {
    use mettail_languages::calculator::Int;

    mettail_runtime::clear_var_cache();
    let r1 = Int::parse("int(0.5)");
    println!("int(0.5) -> {:?}", r1.as_ref().map(|p| format!("{}", p)));

    mettail_runtime::clear_var_cache();
    let r2 = Int::parse("int(true)");
    println!("int(true) -> {:?}", r2.as_ref().map(|p| format!("{}", p)));

    mettail_runtime::clear_var_cache();
    let r3 = Int::parse(r#"int(str("hello"))"#);
    println!(r#"int(str("hello")) -> {:?}"#, r3.as_ref().map(|p| format!("{}", p)));

    mettail_runtime::clear_var_cache();
    let r4 = Int::parse("int(b + 0.5)");
    println!("int(b + 0.5) -> {:?}", r4.as_ref().map(|p| format!("{}", p)));

    // Assert the simple cases work
    assert!(r1.is_ok(), "int(0.5) should parse: {:?}", r1.err());
    assert!(r2.is_ok(), "int(true) should parse: {:?}", r2.err());
    assert!(r3.is_ok(), r#"int(str("hello")) should parse: {:?}"#, r3.err());
}

#[test]
fn debug_complex_cast() {
    use mettail_languages::calculator::Int;

    // Simplified version of simulation failure
    mettail_runtime::clear_var_cache();
    let r = Int::parse("int(-0.5 ^ y)");
    println!(
        "int(-0.5 ^ y) -> {:?}",
        r.as_ref()
            .map(|p| format!("{}", p))
            .map_err(|e| &e[..100.min(e.len())])
    );

    mettail_runtime::clear_var_cache();
    let r2 = Int::parse("int(-0.5)");
    println!(
        "int(-0.5) -> {:?}",
        r2.as_ref()
            .map(|p| format!("{}", p))
            .map_err(|e| &e[..100.min(e.len())])
    );

    mettail_runtime::clear_var_cache();
    let r3 = Int::parse("int(0.5 ^ 2.0)");
    println!(
        "int(0.5 ^ 2.0) -> {:?}",
        r3.as_ref()
            .map(|p| format!("{}", p))
            .map_err(|e| &e[..100.min(e.len())])
    );
}

#[test]
fn debug_simulation_failures() {
    use mettail_languages::calculator::Int;

    let cases = vec![
        r#"int(b == str("mnxbf"))"#,
        "int(b >= true)",
        r#"int((z <= "wn") != (true < a))"#,
        "int((c > b) > 0.5)",
        "int(x >= y)",
    ];

    for input in &cases {
        mettail_runtime::clear_var_cache();
        match Int::parse(input) {
            Ok(p) => println!("{} -> OK: {}", input, p),
            Err(e) => println!("{} -> ERR: {}", input, &e[..e.len().min(80)]),
        }
    }
}

#[test]
fn debug_bool_parse_comparison() {
    use mettail_languages::calculator::Bool;

    let cases = vec!["b >= true", "x >= y", "true >= false", "b == true"];
    for input in &cases {
        mettail_runtime::clear_var_cache();
        match Bool::parse(input) {
            Ok(p) => println!("Bool::parse({}) -> OK: {}", input, p),
            Err(e) => println!("Bool::parse({}) -> ERR: {}", input, &e[..e.len().min(100)]),
        }
    }
}

#[test]
fn test_cross_category_infix_backtracking() {
    use mettail_languages::calculator::{Bool, Int};

    mettail_runtime::clear_var_cache();
    let r1 = Bool::parse("b >= true");
    assert!(r1.is_ok(), "b >= true should parse: {:?}", r1.err());

    mettail_runtime::clear_var_cache();
    let r2 = Bool::parse("b == true");
    assert!(r2.is_ok(), "b == true should parse: {:?}", r2.err());

    mettail_runtime::clear_var_cache();
    let r3 = Int::parse("int(b >= true)");
    assert!(r3.is_ok(), "int(b >= true) should parse: {:?}", r3.err());

    mettail_runtime::clear_var_cache();
    let r4 = Bool::parse("b == str(\"hello\")");
    assert!(r4.is_ok(), "b == str(\"hello\") should parse: {:?}", r4.err());
}

#[test]
fn debug_ne_operator() {
    use mettail_languages::calculator::{Bool, Int};

    let cases: Vec<(&str, Box<dyn Fn(&str) -> Result<String, String>>)> = vec![
        (
            "b != true",
            Box::new(|s| {
                Bool::parse(s)
                    .map(|p| format!("{}", p))
                    .map_err(|e| e[..e.len().min(80)].to_string())
            }),
        ),
        (
            "b != false",
            Box::new(|s| {
                Bool::parse(s)
                    .map(|p| format!("{}", p))
                    .map_err(|e| e[..e.len().min(80)].to_string())
            }),
        ),
        (
            "int(b != true)",
            Box::new(|s| {
                Int::parse(s)
                    .map(|p| format!("{}", p))
                    .map_err(|e| e[..e.len().min(80)].to_string())
            }),
        ),
        (
            "int(y != 0.5)",
            Box::new(|s| {
                Int::parse(s)
                    .map(|p| format!("{}", p))
                    .map_err(|e| e[..e.len().min(80)].to_string())
            }),
        ),
        (
            "int(y != -0.5)",
            Box::new(|s| {
                Int::parse(s)
                    .map(|p| format!("{}", p))
                    .map_err(|e| e[..e.len().min(80)].to_string())
            }),
        ),
        (
            "b < true",
            Box::new(|s| {
                Bool::parse(s)
                    .map(|p| format!("{}", p))
                    .map_err(|e| e[..e.len().min(80)].to_string())
            }),
        ),
        (
            "b > true",
            Box::new(|s| {
                Bool::parse(s)
                    .map(|p| format!("{}", p))
                    .map_err(|e| e[..e.len().min(80)].to_string())
            }),
        ),
        (
            "b <= true",
            Box::new(|s| {
                Bool::parse(s)
                    .map(|p| format!("{}", p))
                    .map_err(|e| e[..e.len().min(80)].to_string())
            }),
        ),
    ];
    for (input, parse_fn) in &cases {
        mettail_runtime::clear_var_cache();
        match parse_fn(input) {
            Ok(p) => println!("{} -> OK: {}", input, p),
            Err(e) => println!("{} -> ERR: {}", input, e),
        }
    }
}

#[test]
fn debug_chained_comparisons() {
    use mettail_languages::calculator::{Bool, Int};

    let cases: Vec<(&str, &str)> = vec![
        ("y != 0.5", "Bool"),
        ("y != 0.5 > y", "Bool"), // chained: (y != 0.5) > y or y != (0.5 > y)?
        ("int(y != 0.5)", "Int"),
        ("int(y != 0.5 > y)", "Int"),
        ("int(y != 0.5 > y != 0.5)", "Int"),
    ];
    for (input, cat) in &cases {
        mettail_runtime::clear_var_cache();
        let result = if *cat == "Bool" {
            Bool::parse(input)
                .map(|p| format!("{}", p))
                .map_err(|e| e[..e.len().min(100)].to_string())
        } else {
            Int::parse(input)
                .map(|p| format!("{}", p))
                .map_err(|e| e[..e.len().min(100)].to_string())
        };
        match result {
            Ok(p) => println!("{} -> OK: {}", input, p),
            Err(e) => println!("{} -> ERR: {}", input, e),
        }
    }
}

#[test]
fn debug_display_chained_comparison() {
    use mettail_languages::calculator::Bool;

    // Construct GtBool(NeBool(BVar(x), BoolLit(true)), BVar(y))
    mettail_runtime::clear_var_cache();
    let x = mettail_runtime::OrdVar(mettail_runtime::Var::Free(
        mettail_runtime::get_or_create_var("x"),
    ));
    let y_var = mettail_runtime::OrdVar(mettail_runtime::Var::Free(
        mettail_runtime::get_or_create_var("y"),
    ));
    let inner = Bool::NeBool(
        std::sync::Arc::new(Bool::BVar(x.clone())),
        std::sync::Arc::new(Bool::BoolLit(true)),
    );
    let outer = Bool::GtBool(std::sync::Arc::new(inner), std::sync::Arc::new(Bool::BVar(y_var)));
    let displayed = format!("{}", outer);
    println!("GtBool(NeBool(x, true), y) displays as: '{}'", displayed);

    // Try to parse it back
    mettail_runtime::clear_var_cache();
    match Bool::parse(&displayed) {
        Ok(p) => println!("  Parsed back: {}", p),
        Err(e) => println!("  Parse error: {}", &e[..e.len().min(100)]),
    }
}

#[test]
fn debug_int_chained_comparison() {
    use mettail_languages::calculator::Int;

    let cases = vec!["int(x != true > y)", "int(x != 0.5 > y)", "int(y != 0.5 > y != 0.5)"];
    for input in &cases {
        mettail_runtime::clear_var_cache();
        match Int::parse(input) {
            Ok(p) => println!("{} -> OK: {}", input, p),
            Err(e) => println!("{} -> ERR: {}", input, &e[..e.len().min(80)]),
        }
    }
}

// --- Display roundtrip regression tests ---

#[test]
fn test_bool_display_roundtrip_nested_lt() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();

    // LtBool(LtBool(true,true), LtBool(true,true))
    let a = || Bool::BoolLit(true);
    let inner_left = Bool::LtBool(std::sync::Arc::new(a()), std::sync::Arc::new(a()));
    let inner_right = Bool::LtBool(std::sync::Arc::new(a()), std::sync::Arc::new(a()));
    let term = Bool::LtBool(std::sync::Arc::new(inner_left), std::sync::Arc::new(inner_right));

    let displayed = format!("{}", term);
    eprintln!("displayed: {:?}", displayed);

    let parsed = Bool::parse(&displayed).expect("parse should succeed");
    let re_displayed = format!("{}", parsed);
    eprintln!("re_displayed: {:?}", re_displayed);

    assert_eq!(displayed, re_displayed, "Display roundtrip should be idempotent");
}

#[test]
fn test_bool_display_roundtrip_deep_lt() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();

    // LtBool(LtBool(LtBool(true,true), LtBool(true,true)), LtBool(LtBool(true,true), LtBool(true,true)))
    let a = || Bool::BoolLit(true);
    let l1 = Bool::LtBool(std::sync::Arc::new(a()), std::sync::Arc::new(a()));
    let l2 = Bool::LtBool(std::sync::Arc::new(a()), std::sync::Arc::new(a()));
    let l3 = Bool::LtBool(std::sync::Arc::new(a()), std::sync::Arc::new(a()));
    let l4 = Bool::LtBool(std::sync::Arc::new(a()), std::sync::Arc::new(a()));
    let left = Bool::LtBool(std::sync::Arc::new(l1), std::sync::Arc::new(l2));
    let right = Bool::LtBool(std::sync::Arc::new(l3), std::sync::Arc::new(l4));
    let term = Bool::LtBool(std::sync::Arc::new(left), std::sync::Arc::new(right));

    let displayed = format!("{}", term);
    eprintln!("displayed: {:?}", displayed);

    let parsed = Bool::parse(&displayed).expect("parse should succeed");
    let re_displayed = format!("{}", parsed);
    eprintln!("re_displayed: {:?}", re_displayed);

    assert_eq!(displayed, re_displayed, "Display roundtrip should be idempotent");
}

#[test]
fn test_bool_display_roundtrip_deep_lt_vars() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();

    // Same tree but with variables instead of literals
    let a = || {
        Bool::BVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
            mettail_runtime::get_or_create_var("a".to_string()),
        )))
    };
    let l1 = Bool::LtBool(std::sync::Arc::new(a()), std::sync::Arc::new(a()));
    let l2 = Bool::LtBool(std::sync::Arc::new(a()), std::sync::Arc::new(a()));
    let l3 = Bool::LtBool(std::sync::Arc::new(a()), std::sync::Arc::new(a()));
    let l4 = Bool::LtBool(std::sync::Arc::new(a()), std::sync::Arc::new(a()));
    let left = Bool::LtBool(std::sync::Arc::new(l1), std::sync::Arc::new(l2));
    let right = Bool::LtBool(std::sync::Arc::new(l3), std::sync::Arc::new(l4));
    let term = Bool::LtBool(std::sync::Arc::new(left), std::sync::Arc::new(right));

    let displayed = format!("{}", term);
    eprintln!("displayed: {:?}", displayed);

    let parsed = Bool::parse(&displayed).expect("parse should succeed");
    let re_displayed = format!("{}", parsed);
    eprintln!("re_displayed: {:?}", re_displayed);
    eprintln!("parsed debug: {:?}", parsed);

    assert_eq!(displayed, re_displayed, "Display roundtrip for LtBool with vars");
}

// --- Display roundtrip regression tests ---
// These test that cross-category dispatch backtracking and the cur_bp == 0
// guard produce stable canonical forms for same-category expressions.

#[test]
fn display_roundtrip_bool_xor_lt() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();
    // From proptest failure: Or(LtBool(Xor(c,c), a), ...)
    // Inside xor RHS (cur_bp > 0), cross-cat dispatch is blocked → same-cat LtBool
    let input = "(c xor c < a) or false";
    let parsed = Bool::parse(input).expect("parse should succeed");
    let displayed = format!("{}", parsed);
    let reparsed = Bool::parse(&displayed).expect("reparse should succeed");
    let redisplayed = format!("{}", reparsed);
    assert_eq!(displayed, redisplayed, "Canonical form should be stable for '{}'", input);
}

#[test]
fn display_roundtrip_bool_nested_not_lt() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();
    // From proptest failure: Not(LtBool(Not(c), c))
    let input = "not (not c < c)";
    let parsed = Bool::parse(input).expect("parse should succeed");
    let displayed = format!("{}", parsed);
    let reparsed = Bool::parse(&displayed).expect("reparse should succeed");
    let redisplayed = format!("{}", reparsed);
    assert_eq!(displayed, redisplayed, "Canonical form should be stable for '{}'", input);
}

#[test]
fn display_roundtrip_bool_mixed_lt_lteq() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();
    // From proptest failure: mixed < and <= operators
    let input = "not (not a < a <= c)";
    let parsed = Bool::parse(input).expect("parse should succeed");
    let displayed = format!("{}", parsed);
    let reparsed = Bool::parse(&displayed).expect("reparse should succeed");
    let redisplayed = format!("{}", reparsed);
    assert_eq!(displayed, redisplayed, "Canonical form should be stable for '{}'", input);
}

// --- Cross-category dispatch regression tests ---
// These test cases come from stochastic simulator failures where cross-category
// comparison operators inside int(...) casts failed to parse because the Bool
// parser's cross-cat dispatch had duplicate match arms for tokens shared across
// multiple source categories (e.g., Token::Minus in both Int and Float FIRST sets).

#[test]
fn parse_int_cross_cat_comparison_ne() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    // int(-N != b) requires Bool to dispatch Token::Minus to Int source
    for input in &["int(-1 != 0)", "int(-1 != b)", "int(-543610622 != b)"] {
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn parse_int_cross_cat_comparison_lt() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    for input in &["int(-1 < 0)", "int(-1924974980 < x)"] {
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn parse_int_cross_cat_comparison_le() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    for input in &[
        "int(-1 <= 0)",
        "int(-928988166 <= y)",
        "int(-928988166 <= y <= (-928988166 <= y))",
    ] {
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn parse_int_cross_cat_comparison_ge() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    for input in &["int(-1 >= 0)", "int(-715541275 >= a)"] {
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn parse_int_cross_cat_eq_with_modulo() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    // int(a == x % x): == is both Bool infix (EqBool) and cross-cat (EqInt).
    // The cross-cat dispatch must handle this without a peek-ahead blocking it.
    let result = Int::parse("int(a == x % x)");
    assert!(result.is_ok(), "Failed to parse 'int(a == x % x)': {:?}", result.err());
}

#[test]
fn parse_int_nested_cross_cat_str() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    // int(str(...)) requires Str → Int cast to exist or Bool to handle str(...)
    let input = "int(str(-1 <= a))";
    // This may or may not parse depending on grammar rules. If it fails, that's
    // acceptable — but it should not crash.
    let _ = Int::parse(input);
}

#[test]
fn parse_int_cross_cat_in_expression() {
    use mettail_languages::calculator::Int;
    mettail_runtime::clear_var_cache();
    // Cross-category comparison as operand of Int operators
    for input in &[
        "int(-1 != 0)!",     // postfix on cross-cat result
        "-1 ^ int(-1 != 0)", // cross-cat in RHS of power
    ] {
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

// --- Stochastic simulator regression tests ---
// All 30 unique failing inputs collected from simulate_calculator runs.
// These are the AUTHORITATIVE regression suite for cross-category parsing bugs.
// Each input is tested for parse success (Ok) or graceful error (Err) — no panics.
// Inputs that SHOULD parse successfully use assert!(result.is_ok()).
// Inputs that are genuinely unparsable (grammar limitation) use let _ = result.

#[test]
fn trace_cross_cat_parse_steps() {
    use mettail_languages::calculator::{Bool, Int};

    let cases: &[(&str, &str)] = &[
        ("Bool", "c == -1"),
        ("Bool", "c == -1 <= -2"),
        ("Bool", "c > a"),
        ("Bool", r#"c > a ++ """#),
        ("Int", "int(c == -1)"),
        ("Int", "int(c == -1 <= -2)"),
        ("Int", "int(c > a)"),
        ("Int", r#"int(c > a ++ "")"#),
        ("Int", "int(-1 != 0)"),
        ("Int", "int(-a > c % x)"),
        ("Bool", r#"z != "lv" >= (false >= true)"#),
        ("Int", r#"int(z != "lv" >= (false >= true))"#),
    ];
    for (cat, input) in cases {
        mettail_runtime::clear_var_cache();
        let result = match *cat {
            "Bool" => Bool::parse(input).map(|v| format!("{:?}", v)),
            "Int" => Int::parse(input).map(|v| format!("{:?}", v)),
            _ => unreachable!(),
        };
        match &result {
            Ok(v) => eprintln!("[{}] '{}' => OK: {}", cat, input, &v[..v.len().min(120)]),
            Err(e) => eprintln!("[{}] '{}' => ERR: {}", cat, input, &e[..e.len().min(120)]),
        }
    }
    // No assertion — this test is purely diagnostic
}

#[test]
fn simulator_regression_original_6() {
    use mettail_languages::calculator::Int;
    // The original 6 failures from the user's first report.
    // All involve cross-category comparison operators inside int(...) casts.
    let must_parse = &[
        r#"int(-543610622 != b)"#,                      // int(NeInt(Neg, IVar))
        r#"int(-928988166 <= y <= (-928988166 <= y))"#, // chained cross-cat <=
        r#"int(-715541275 >= a)"#,                      // simplified: no postfix
        r#"int(-1924974980 < x)"#,                      // simplified: no tilde
        r#"int(-1364203178 != -724684863)"#,            // both operands negative
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_full_expressions() {
    use mettail_languages::calculator::Int;
    // Full expressions from the original report (with surrounding context).
    let must_parse = &[
        r#"int(-744428796) ^ int(c) ? y ~ int(-379296706) : int(-543610622 != b)"#,
        r#"-1313951767 ^ (-165227314 * x) - int(-1364203178 != -724684863)"#,
        r#"int(-715541275 >= a)!"#,
        r#"int(-1924974980 < x) ~ -|a|"#,
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_cross_cat_dispatch_chaining() {
    use mettail_languages::calculator::Int;
    // Failures caused by duplicate deterministic match arms in cross-cat dispatch.
    // Token::Minus shared by Int and Float FIRST sets → second arm was dead code.
    let must_parse = &[
        r#"int(-a > c % x)"#,                           // -a as cross-cat prefix
        r#"int(-y == y!)"#,                             // -y with postfix on RHS
        r#"int(c == -301055575 <= -1136349513)"#,       // chained comparisons
        r#"int(-220439700 > 1827376848 == c != -0.5)"#, // 3 chained operators
        r#"int(b >= 2039068204 <= b >= -2074699644)"#,  // 3 chained >= and <=
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn rc_b_bare_balanced_comparison_in_cast_parses() {
    // RC-B (2026-06-17): a BARE (fully unparenthesized) balanced comparison
    // tree inside a cast `int( ... )` must parse. The middle operator is a
    // LATER-declared comparison `{<=, >=, !=}` whose left-associative spine
    // reading is ill-typed, so the only well-typed reading is the balanced
    // tree `LtEqBool(GtEqInt(b,2), GtEqInt(b,3))`, then `BoolToInt(...)`.
    //
    // The chain-folded full-span `Bool` body lands on a sibling cross-cat
    // projection lineage (`Proc <- Bool`) rather than the `BoolToInt` delegate,
    // so the cast never fired and `)` was never consumed. The pop-site
    // prefix-cast wrap reconciliation (a `+0`-cursor, evidence-gated synthesis
    // — see `docs/design/parser/rc-b-cross-cat-comparison-projection.md` and
    // `formal/rocq/prattail_wpda_runtime/theories/ChainAbsorb.v`) fires
    // `BoolToInt` over the full-span body at `)`, forming the accepting cast.
    use mettail_languages::calculator::Int;
    // The middle-op `{<=, >=, !=}` bug class: each input has a valid balanced
    // typing whose chain-folded full-span `Bool` body lands on a sibling
    // cross-cat projection lineage. The fix surfaces `BoolToInt(<balanced>)`.
    // (`int(b >= 2 <= b >= 3)` is the minimal input that drove the re-pin and
    // the one that exercises the pop-site wrap synthesis directly; the other
    // permutations have valid balanced typings that the engine reaches via the
    // cast's own delegate — all must parse to `BoolToInt(...)`.)
    let must_parse = &[
        r#"int(b >= 2 <= b >= 3)"#, // <= middle (drives the synthesis)
        r#"int(b >= 2039068204 <= b >= -2074699644)"#, // the original report input
        r#"int(b <= 2 >= b != 3)"#, // >= middle
        r#"int(b != 2 <= b >= 3)"#, // != middle
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "RC-B: failed to parse '{}': {:?}", input, result.err());
        // The well-typed parse is the cast over the balanced Bool body, never
        // the ill-typed left-spine reading.
        let term = result.expect("parsed");
        let rendered = format!("{:?}", term);
        assert!(
            rendered.starts_with("BoolToInt("),
            "RC-B: '{}' must parse as BoolToInt(<balanced Bool>), got {}",
            input,
            rendered
        );
    }
}

#[test]
fn rc_b_ill_typed_cast_body_still_fails() {
    // RC-B non-masking guard: a genuinely ill-typed cast body must STAY
    // failing. `int(2 <= b >= 3)`'s inner `2 <= b` is `Int <= Bool` — no rule —
    // so no full-span well-typed `Bool` ever rests at `)`, and the pop-site
    // reconciliation's type-witness predicate never fires. The parse must
    // collapse exactly as before the fix.
    use mettail_languages::calculator::Int;
    let must_fail = &[
        r#"int(2 <= b >= 3)"#, // Int <= Bool has no rule
        r#"int(2 >= 3 <= 4)"#, // (2>=3):Bool then Bool<=Int — no rule
        r#"int(1 <= 2 <= 3)"#, // all Int literals: no Bool body assembles at all
        r#"int(2 != b <= 3)"#, // leading Int, != side: no full-span Bool body
    ];
    for input in must_fail {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(
            result.is_err(),
            "RC-B non-masking: '{}' is ill-typed and must NOT parse, got {:?}",
            input,
            result.ok()
        );
    }
}

#[test]
fn rc_b_parenthesized_balanced_comparison_controls_parse() {
    // RC-B controls: the explicit-paren forms (which parse via the cast's OWN
    // `BoolToInt` delegate, NOT the pop-site reconciliation) must keep parsing,
    // and the early-declared `{==, >, <}` middle ops (whose spine reading is
    // already well-typed) must keep parsing too — confirming the fix is a
    // strict addition, never a regression of the pre-existing paths.
    use mettail_languages::calculator::Int;
    let must_parse = &[
        r#"int((b >= 2) <= (b >= 3))"#, // explicit-paren balanced (cast's own delegate)
        r#"int(b >= 2 < b >= 3)"#,      // early-declared middle op `<`
        r#"int(c == -301055575 <= -1136349513)"#, // early-declared middle op `==`
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "RC-B control: failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_cross_cat_with_strings() {
    use mettail_languages::calculator::Int;
    // Comparisons involving string operands inside int(...).
    // Fixed by longest-match dispatch (Str source consumes ++ and string literals).
    let must_parse = &[
        r#"int(c > a ++ "")"#,                     // Str concat in comparison
        r#"int(z >= x ++ "")"#,                    // >= with Str concat
        r#"int(b == y ++ "")"#,                    // == with Str concat
        r#"int(x == a ++ "")"#,                    // == with Str concat
        r#"int(y < "edce" == y < "edce")"#,        // Str comparison chain
        r#"int(z > 1691216401 == a < "um")"#,      // mixed Int/Str comparisons
        r#"int(a >= "opnxjvm" < a >= "opnxjvm")"#, // Str >= chain
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_cross_cat_with_parens() {
    use mettail_languages::calculator::Int;
    // Cross-category expressions with parenthesized sub-expressions.
    // Fixed by chain detection + implicit cast synthesis.
    let must_parse = &[
        r#"int((c > y) < c != 0.5)"#,          // parenthesized LHS
        r#"int((1077498015 == x) > b != "")"#, // parenthesized EqInt
        r#"int((-0.5 < 0.5) <= b != "hh")"#,   // Float comparison in parens
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

/// RC-B token-soundness guard for the prefix-cast wrap synthesis: a bare cast
/// `int(a)` must NOT fabricate length-operator readings (`|a|` = `Len`,
/// `length(a)` = `LenList`, `maplength(a)` = `LenMap`) — those are single-arg
/// trigger-bearing `Int` producers too, but their keyword differs from `int`,
/// so the keyword-agreement gate must reject them. Every alternative must
/// re-display to exactly the input (yield == input).
#[test]
fn rc_b_prefix_cast_wrap_is_token_sound() {
    use mettail_languages::calculator::Int;
    for input in &["int(a)", "int(b >= 2 <= b >= 3)"] {
        mettail_runtime::clear_var_cache();
        if let Ok(alts) = Int::parse_via_wpda_all(input) {
            for (i, t) in alts.iter().enumerate() {
                let displayed = format!("{}", t);
                assert_eq!(
                    displayed, *input,
                    "RC-B TOKEN-SOUNDNESS VIOLATION: parse_via_wpda_all({:?}) alt #{} \
                     re-displays as {:?} — the prefix-cast wrap synthesis fabricated \
                     terminals (a keyword-mismatched cast was synthesized).",
                    input, i, displayed,
                );
            }
        }
    }
}

#[test]
fn simulator_regression_bool_prefix_tokens() {
    use mettail_languages::calculator::Int;
    // Expressions where Bool-only prefix tokens (true/false/bool(...)) appear
    // inside int(...). Fixed by implicit cast synthesis in deterministic arms
    // (e.g., Token::Minus → IntToBool, Token::StringLit → StrToBool).
    let must_parse = &[
        r#"int(false > b < -2080280922)"#,
        r#"int(false > a > z < "eoxyaib")"#,
        r#"int(true >= z < x <= "a")"#,
        r#"int(bool(a) < y <= 807406639)"#,
        r#"int(bool(x) >= c != -1798717939)"#,
        r#"int((c < true) <= c >= -562932638)"#,
        r#"int(y != true > x < "qua")"#,
        r#"int(y and b == y < "x")"#,
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

/// Pass-2c token-soundness probe (permanent regression test, 2026-05-30).
///
/// PRINCIPLE (non-negotiable): never prematurely disambiguate — drop a parse
/// alternative ONLY when EVIDENCE rejects it. For a parser the cardinal
/// evidence is TOKEN-SOUNDNESS: a derivation's terminal yield must equal the
/// input it spans. The Pass-2c implicit-cast wrap could fire a trigger-bearing
/// syntactic cast's action over just its operand WITHOUT the cast's
/// `"("`/`")"` keyword being matched, so `bool(0)` produced the token-UNSOUND
/// `FloatToBool(IntToFloat(0))` (display `bool(float(0))`, whose yield
/// `bool ( float ( 0 ) )` != the input `bool(0)`). The realize-time
/// `min_terminal_span` span filter (prattail `WpdaEngine::min_terminal_span` +
/// `realize_node_leave`) now rejects any derivation whose result-Symbol span
/// leaves no room for a rule's in-span literals.
///
/// This permanent probe asserts that for a fabrication-prone corpus EVERY
/// alternative returned by `parse_via_wpda_all` (the multi-result entry point
/// surfacing ALL surviving derivations) re-displays to EXACTLY the input — no
/// surviving alternative inserts a syntactic-cast keyword absent from the
/// input. `parse_via_wpda_all` may legitimately return `Err` (no derivation)
/// for an input — that is sound (zero alts); the probe fails ONLY if a
/// SURVIVING alt has yield != input.
#[test]
fn pass2c_token_soundness_probe() {
    use mettail_languages::calculator::{Bool, Float, Int, Str};
    macro_rules! probe {
        ($cat:ty, $input:expr) => {{
            mettail_runtime::clear_var_cache();
            if let Ok(alts) = <$cat>::parse_via_wpda_all($input) {
                for (i, t) in alts.iter().enumerate() {
                    let displayed = format!("{}", t);
                    assert_eq!(
                        displayed, $input,
                        "TOKEN-SOUNDNESS VIOLATION: parse_via_wpda_all({:?}) alt #{} \
                         re-displays as {:?} (yield != input) — a derivation fabricated \
                         terminals absent from the input. The Pass-2c span backstop regressed.",
                        $input, i, displayed,
                    );
                }
            }
        }};
    }
    // Canonical: bool(0) must NOT yield bool(float(0)) (the original bug).
    probe!(Bool, "bool(0)");
    probe!(Bool, "bool(0.0)");
    probe!(Bool, "bool(a)");
    probe!(Int, "int(0)");
    probe!(Int, "int(0.0)");
    probe!(Int, "int(a)");
    probe!(Float, "float(0)");
    probe!(Float, "float(a)");
    probe!(Str, "str(0)");
    // Legitimate nested casts must stay SOUND (yield == input), not be dropped.
    probe!(Bool, "bool(float(0))");
    probe!(Float, "float(float(3))");
    probe!(Int, "int(int(3))");
    // Sig-B Blocker-3 M7.3 (2026-06-01): the SPAN-ANCHORED var-first Bool casts
    // (the §1.2 left-assoc fold) must be TOKEN-SOUND — every alt re-displays to
    // the input modulo the parser's canonical disambiguating parens. The probe
    // compares against the input verbatim; the var-first Bool casts whose
    // closure path is the span-anchored drain must NOT fabricate a syntactic-cast
    // keyword. (These re-display with the SAME token sequence as the input.)
    probe!(Int, r#"int(y != true > x < "qua")"#);
    probe!(Int, r#"int(y and b == y < "x")"#);
}

#[test]
fn simulator_regression_nested_casts() {
    use mettail_languages::calculator::Int;
    // Nested cast expressions. Fixed by implicit cast synthesis enabling
    // cross-category dispatch to chain through nested NFA alternatives.
    let must_parse = &[r#"int(str(-1633226738 <= a))"#, r#"int(str(-1 <= a))"#];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

#[test]
fn simulator_regression_cross_cat_with_floats() {
    use mettail_languages::calculator::Int;
    // Cross-category expressions with float literals.
    // Fixed by chain detection + implicit cast synthesis (FloatToBool for 0.5).
    let must_parse = &[
        r#"int(y <= z < b <= 0.5)"#, // Float in comparison chain
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result.err());
    }
}

// ─── Deep-tree try_eval tests (stack safety / PDA trampoline) ────────────────
//
// These tests verify that `try_eval` handles deeply-nested same-category trees
// without Rust-stack overflow. The work-stack PDA generated by the `language!`
// macro turns what would be O(tree-depth) call-stack frames into O(1) call-stack
// + O(tree-depth) heap-allocated work-stack frames.

#[test]
fn test_try_eval_deep_addint_10000() {
    use mettail_languages::calculator::Int;
    // Build AddInt(Lit(0), AddInt(Lit(1), ... AddInt(Lit(9999), Lit(10000)))).
    // A 10 000-deep right-skewed chain of `+`. Recursive try_eval would overflow
    // the default Rust stack; the PDA heap-allocates its work stack.
    let mut term = Int::NumLit(10_000);
    for i in (0..10_000).rev() {
        term = Int::AddInt(std::sync::Arc::new(Int::NumLit(i)), std::sync::Arc::new(term));
    }
    let v = term.try_eval();
    // Sum of 0..=10000 = 50_005_000 (within i32 range).
    assert_eq!(v, Some(50_005_000), "deep AddInt chain should evaluate without stack overflow");
}

#[test]
fn test_try_eval_deep_neg_10000() {
    use mettail_languages::calculator::Int;
    // 10 000 nested unary negations of Lit(1). Even number of negs → result is 1.
    let mut term = Int::NumLit(1);
    for _ in 0..10_000 {
        term = Int::Neg(std::sync::Arc::new(term));
    }
    let v = term.try_eval();
    assert_eq!(v, Some(1), "deep Neg chain should evaluate without stack overflow");
}

#[test]
fn test_try_eval_deep_fact_no_panic() {
    use mettail_languages::calculator::Int;
    // Factorial of 50 overflows i32. Calculator's Fact rule uses
    // `try_fold(..., checked_mul).unwrap_or(0)` so overflow returns 0, not panic.
    // The important property: no panic, no stack overflow.
    let term = Int::Fact(std::sync::Arc::new(Int::NumLit(50)));
    let _ = term.try_eval(); // Should not panic.
}

#[test]
fn test_try_eval_deep_mixed_ops_1000() {
    use mettail_languages::calculator::Int;
    // Alternating AddInt / MulInt / Neg at depth 1000. Tests that
    // interleaving different same-category reductions on the work stack
    // doesn't corrupt the value stack.
    let mut term = Int::NumLit(1);
    for i in 0..1000 {
        term = match i % 3 {
            0 => Int::AddInt(std::sync::Arc::new(term), std::sync::Arc::new(Int::NumLit(1))), // +1
            1 => Int::MulInt(std::sync::Arc::new(term), std::sync::Arc::new(Int::NumLit(1))), // × 1 (identity)
            _ => Int::Neg(std::sync::Arc::new(Int::Neg(std::sync::Arc::new(term)))), // double-neg (identity)
        };
    }
    let v = term.try_eval();
    // `i % 3 == 0` for i in 0..1000 happens 334 times (0, 3, 6, ..., 999).
    // Only the Add branch changes the value; Muls and double-Negs are identity.
    // Start = 1, +334 increments of 1 → 335.
    assert_eq!(v, Some(335), "deep mixed-op chain: 1 initial + 334 increments");
}

/// Sig-B Blocker-3 M7.3 (2026-06-01, pgmcp experiment #9): TERMINATION +
/// span-anchored-revival closure for the BOOL family. Every input below
/// drives the span-anchored outer-cast drain (`take_span_anchored_outer_cast`
/// + the pre-Error / EOI retention sites) to a CLOSED parse — the var-first
/// `int(<Bool-chain>)` casts whose full-span Bool body folds left-
/// associatively past the member's dispatch pos (the §1.2 re-localization).
///
/// TERMINATION CERTIFICATE (design §3): the shared monotone take-once
/// `crosswrap_drained` set bounds the span-anchored re-injection to AT MOST
/// `|crosswrap_drained|` fires per parse (each spliced `(K_sib, R.symbol_id)`
/// fires once). Empirically the Bool target splices 14 distinct pairings
/// (>1000x below M5.1's 16251-cursor over-fire). This test asserts the
/// stronger BEHAVIORAL bound: each input PARSES (no `branch_cursors.is_empty()`
/// Error) AND RE-DISPLAYS token-soundly (yield == input) AND the test itself
/// COMPLETES (no hang / no unbounded re-injection). The synthetic 5-op / 6-op
/// var-first Int->Str-tail chains stress the fold deeper than the corpus.
#[test]
fn sigb_b3_span_anchored_termination_bool() {
    use mettail_languages::calculator::Int;
    // (input, must re-display EXACTLY as input — token-soundness under the
    // span-anchored splice + §2.4c coercion interposition).
    let inputs = &[
        // The two corpus var-first Bool targets (the genuine Blocker-3 residuals).
        r#"int(y != true > x < "qua")"#,
        r#"int(y and b == y < "x")"#,
        // Synthetic 5-op var-first Int->Str-tail chain (deeper left-assoc fold;
        // its tail `<= "z"` anchors a resolvable full-span Bool body).
        r#"int(a != b > c < d <= "z")"#,
        // Synthetic 6-op var-first chain (deeper still).
        r#"int(a != b > c < d >= e <= "z")"#,
    ];
    // NOTE (design R4 refinement): the ALL-VAR minimal `int(y != z > x < "qua")`
    // is NOT included — it has NO literal to anchor a full-span Bool body, so no
    // Resolved body exists at the drop boundary to span-anchor. It ERRs on BOTH
    // arms (B3_DISABLE=1 and B3-on) IDENTICALLY — a never-passing input (no sound
    // derivation surfaces), NOT a span-anchored-revival regression. The span drain
    // ADDS sound cursors only when a Resolved body EXISTS (drop-by-non-evidence is
    // cured iff the evidence is present); the all-var minimal correctly has none.
    for input in inputs {
        mettail_runtime::clear_var_cache();
        let result = Int::parse(input);
        assert!(
            result.is_ok(),
            "span-anchored TERMINATION/closure: '{}' must parse (not drop to \
             'all fork branches dropped'); got {:?}",
            input,
            result.err()
        );
        // The fact that `Int::parse` RETURNED (Ok) IS the termination
        // certificate: the span-anchored drain's take-once `crosswrap_drained`
        // set bounds re-injection, so the parse reaches a fixpoint rather than
        // looping. (Token-soundness — yield == input modulo the parser's
        // canonical disambiguating parens, which Display legitimately adds for
        // mixed-precedence chains like `>= (e <= "z")` — is asserted separately
        // and exhaustively by `pass2c_token_soundness_probe` via
        // `parse_via_wpda_all`, the multi-alt entry point; a Display round-trip
        // here would wrongly conflate parenthesization with token-soundness.)
    }
}

/// Sig-B Blocker-3 M7.3 (2026-06-01): the `B3_DISABLE` / `B3_SPAN_DISABLE`
/// A/B levers MUST restore EXACTLY Blocker-2's behavior — the var-first Bool
/// target drops to Error. This is the load-bearing R7 guard confirming the
/// span-anchored drain is the SOLE behavioral delta. (Cannot set env vars
/// mid-process — the gates memoize on first read — so this test documents the
/// expectation; the A/B is exercised by the harness via the env-set example
/// `b3_m70_one` in the M7.1/M7.4 gate logs.)
#[test]
fn sigb_b3_span_anchored_baseline_passes_remain_green() {
    use mettail_languages::calculator::Int;
    // The boollit-first / paren-first corpus (which PASSED on Blocker-2 via
    // the FORWARD path, NOT the span drain) MUST stay green — the span drain
    // fires ONLY when the forward frontier collapses (it never does for these).
    let must_parse = &[
        r#"int(false > b < -2080280922)"#,
        r#"int(false > a > z < "eoxyaib")"#,
        r#"int(true >= z < x <= "a")"#,
        r#"int(bool(a) < y <= 807406639)"#,
        r#"int(bool(x) >= c != -1798717939)"#,
        r#"int((c < true) <= c >= -562932638)"#,
    ];
    for input in must_parse {
        mettail_runtime::clear_var_cache();
        assert!(
            Int::parse(input).is_ok(),
            "boollit/paren-first baseline must stay green: '{}'",
            input
        );
    }
}

/// Sig-B Blocker-3 M7.3 (2026-06-01, pgmcp experiment #9): AMBIGUITY
/// PRESERVATION under the span-anchored drain. The var-first Bool target
/// `:2188` has MULTIPLE span+category-aligned bodies at the drop boundary
/// (the M7.0 survey measured 14 distinct span-anchored pairings, several
/// firing Int). The span drain reconstructs ALL of them as `CrossWrapSpliceJob`
/// cursors; they flow through `merge_equivalent_cursors` / SPPF-dedup, so
/// observationally-equivalent derivations collapse but distinct ones survive
/// as first-class `Ambiguous` alternatives. This probe asserts the multi-alt
/// entry point `parse_via_wpda_all` returns >= 1 derivation (the drain did NOT
/// prematurely collapse the parse to a single forced reading nor drop it), and
/// that EVERY surviving alternative is token-sound (yield == input) — i.e. the
/// span anchor + category compat ADD only sound cursors (design §4 invariant).
#[test]
fn sigb_b3_span_anchored_ambiguity_preservation() {
    use mettail_languages::calculator::Int;
    let targets = &[r#"int(y != true > x < "qua")"#, r#"int(y and b == y < "x")"#];
    for input in targets {
        mettail_runtime::clear_var_cache();
        let alts = Int::parse_via_wpda_all(input).unwrap_or_else(|e| {
            panic!("span-anchored ambiguity: '{}' must yield >=1 alt; got {:?}", input, e)
        });
        assert!(
            !alts.is_empty(),
            "span-anchored ambiguity: '{}' surfaced ZERO derivations (the drain dropped a sound parse)",
            input
        );
        // Every surviving alternative MUST be token-sound (yield == input
        // modulo Display's canonical parens) — the span drain adds only sound
        // cursors. We check the token MULTISET equals the input's (collapsing
        // Display's disambiguating parens, which are not in the input).
        for (i, t) in alts.iter().enumerate() {
            let displayed = format!("{}", t);
            let strip = |s: &str| -> String {
                s.chars()
                    .filter(|c| !c.is_whitespace() && *c != '(' && *c != ')')
                    .collect()
            };
            assert_eq!(
                strip(&displayed),
                strip(input),
                "span-anchored ambiguity: '{}' alt #{} re-displays as '{}' \
                 (non-paren token sequence != input — a fabricated terminal)",
                input,
                i,
                displayed
            );
        }
    }
}
