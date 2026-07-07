use mettail_languages::{calculator, rhocalc};
use mettail_prattail::wpda_runtime::{LatticeTokenSource, WpdaTokenSource};

#[test]
fn rhocalc_name_keyword_text_uses_identifier_alternative() {
    let parsed = rhocalc::Name::parse_via_wpda("merge")
        .expect("Name parser should accept identifier text that is a Proc keyword");
    assert!(matches!(parsed, rhocalc::Name::NVar(_)), "got {:?}", parsed);
}

#[test]
fn rhocalc_name_keyword_text_uses_identifier_alternative_in_structured_parse() {
    let parsed = rhocalc::Name::parse_structured("merge")
        .expect("structured Name parser should share the WPDA lattice backend");
    assert!(matches!(parsed, rhocalc::Name::NVar(_)), "got {:?}", parsed);
}

#[test]
fn rhocalc_name_keyword_text_uses_identifier_alternative_in_string_parse() {
    let parsed = rhocalc::Name::parse("merge")
        .expect("string Name parser should share the WPDA lattice backend");
    assert!(matches!(parsed, rhocalc::Name::NVar(_)), "got {:?}", parsed);
}

#[test]
fn rhocalc_name_keyword_text_uses_identifier_alternative_in_all_parse() {
    let parsed = rhocalc::Name::parse_via_wpda_all("merge")
        .expect("all-results Name parser should share the WPDA lattice backend");
    assert!(
        parsed
            .iter()
            .any(|term| matches!(term, rhocalc::Name::NVar(_))),
        "got {:?}",
        parsed
    );
}

/// Operator-form negatives (merge decision #4): the calculator `Int` regex
/// dropped the leading `-?`, so `-3!` no longer forks in the lex DAG into an
/// atomic-negative `Fact(NumLit(-3))` branch. The source-generic WPDA facade
/// (`parse_Int_via_wpda_all_with_source`) therefore returns the single
/// operator-form reading `Neg(Fact(NumLit(3)))`, with one realized weight, and
/// consumes the whole DAG. This test guards that operator-form behavior plus the
/// one-weight-per-term invariant of the all-results facade.
#[test]
fn calculator_parse_all_with_source_returns_weight_for_each_neg_factorial_alternative() {
    let dag = calculator::lex_dag("-3!").expect("calculator lex DAG should accept -3!");
    assert!(
        !dag.has_ambiguity(),
        "-3! must NOT fork in the lex DAG under operator-form negatives (no atomic-negative literal)",
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
    // The removed atomic-negative branch must NOT reappear.
    assert!(
        !terms.iter().any(|t| {
            matches!(
                t,
                calculator::Int::Fact(a)
                    if matches!(a.as_ref(), calculator::Int::NumLit(-3))
            )
        }),
        "atomic-negative branch Fact(NumLit(-3)) must NOT be produced; got {:?}",
        terms
    );
}
