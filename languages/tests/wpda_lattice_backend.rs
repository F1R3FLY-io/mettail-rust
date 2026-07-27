use mettail_languages::{calculator, rholang};
use mettail_prattail::wpda_runtime::{LatticeTokenSource, WpdaTokenSource};

#[test]
fn rholang_name_keyword_text_uses_identifier_alternative() {
    let parsed = rholang::Name::parse_via_wpda("merge")
        .expect("Name parser should accept identifier text that is a Proc keyword");
    assert!(matches!(parsed, rholang::Name::NVar(_)), "got {:?}", parsed);
}

#[test]
fn rholang_name_keyword_text_uses_identifier_alternative_in_structured_parse() {
    let parsed = rholang::Name::parse_structured("merge")
        .expect("structured Name parser should share the WPDA lattice backend");
    assert!(matches!(parsed, rholang::Name::NVar(_)), "got {:?}", parsed);
}

#[test]
fn rholang_name_keyword_text_uses_identifier_alternative_in_string_parse() {
    let parsed = rholang::Name::parse("merge")
        .expect("string Name parser should share the WPDA lattice backend");
    assert!(matches!(parsed, rholang::Name::NVar(_)), "got {:?}", parsed);
}

#[test]
fn rholang_name_keyword_text_uses_identifier_alternative_in_all_parse() {
    let parsed = rholang::Name::parse_via_wpda_all("merge")
        .expect("all-results Name parser should share the WPDA lattice backend");
    assert!(
        parsed
            .iter()
            .any(|term| matches!(term, rholang::Name::NVar(_))),
        "got {:?}",
        parsed
    );
}

/// ★ RE-DERIVED 2026-07-27 (ledger D1 in
/// `languages/tests/literal_domain_agreement.rs`). The SUBJECT is the one-weight-per-term
/// invariant of the source-generic all-results facade
/// (`parse_Int_via_wpda_all_with_source`) over a LATTICE token source, and the test's
/// whole reason to use a lattice source is that the source FORKS.
///
/// Under "merge decision #4" the calculator `Int` regex had dropped its leading `-?`, so
/// `-3!` stopped forking and the test asserted `!dag.has_ambiguity()` — at which point it
/// was exercising the facade over a degenerate, linear DAG and could not have detected a
/// weight/term mismatch on a forked one. D1 restored the sign to the `Int` literal, so the
/// DAG forks again and the assertion is inverted to say so: the fork is the PRECONDITION
/// of the invariant under test, not an incidental property.
#[test]
fn calculator_parse_all_with_source_returns_weight_for_each_neg_factorial_alternative() {
    let dag = calculator::lex_dag("-3!").expect("calculator lex DAG should accept -3!");
    assert!(
        dag.has_ambiguity(),
        "-3! MUST fork in the lex DAG — the `Int` literal is signed (D1), so `-3` is both \
         one token and two; a linear DAG here would make the one-weight-per-term assertion \
         below vacuous",
    );
    let source = LatticeTokenSource::new(dag);
    let mut pos = 0usize;
    let (terms, weights) = calculator::parse_Int_via_wpda_all_with_source(&source, &mut pos, 0)
        .expect("-3! should parse through the source-generic WPDA facade");

    assert_eq!(pos, source.eof_node(), "parse should reach the DAG EOF node");
    assert_eq!(
        terms.len(),
        weights.len(),
        "all-results facade must return one realized weight per term",
    );
    // Operator-form reading -(3!) = Neg(Fact(NumLit(3))).
    assert!(
        terms.iter().any(|t| {
            matches!(
                t,
                calculator::Int::Neg(a)
                    if matches!(
                        a.as_ref(),
                        calculator::Int::Fact(b)
                            if matches!(b.as_ref(), calculator::Int::NumLit(3))
                    )
            )
        }),
        "expected operator-form reading Neg(Fact(NumLit(3))); got {:?}",
        terms
    );
    // …and the atomic-negative reading (-3)! = Fact(NumLit(-3)), the other side of the
    // fork, so `terms.len() == weights.len()` above is checked on a genuinely multi-term
    // realization rather than a singleton.
    assert!(
        terms.iter().any(|t| {
            matches!(
                t,
                calculator::Int::Fact(a)
                    if matches!(a.as_ref(), calculator::Int::NumLit(-3))
            )
        }),
        "expected atomic-negative reading Fact(NumLit(-3)); got {:?}",
        terms
    );
}
