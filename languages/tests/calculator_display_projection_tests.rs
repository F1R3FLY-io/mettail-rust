use mettail_languages::calculator::{BigInt, BigRat, Bool, Fixed, Float, Str, UInt32};
use mettail_prattail::automata::TokenKind;
use std::sync::Arc;

#[test]
fn calculator_error_keyword_survives_identifier_lex_ambiguity() {
    mettail_runtime::clear_var_cache();

    let dag = mettail_languages::calculator::lex_dag("error").expect("lex dag should build");
    let root_edges = &dag.nodes[0].edges;
    assert!(
        root_edges.len() > 1,
        "same-span keyword/identifier ambiguity should stay in the DAG: {root_edges:?}"
    );
    assert!(
        root_edges
            .iter()
            .any(|edge| { matches!(&edge.kind, TokenKind::Fixed(text) if text == "error") }),
        "error keyword edge should survive beside identifier edges: {root_edges:?}"
    );
    assert!(
        root_edges
            .iter()
            .any(|edge| matches!(&edge.kind, TokenKind::Ident)),
        "identifier edge should remain available as an alternative: {root_edges:?}"
    );

    BigRat::parse("error").expect("BigRat parser should choose the error keyword path");
    BigRat::parse("(error / 658533982)")
        .expect("BigRat infix parser should keep keyword evidence inside grouping");
    BigRat::parse("(error / 658533982) bitand 3521345456")
        .expect("grouped BigRat division should continue into bitand");
    BigRat::parse("(error / 658533982) bitand (709677539 / -2024700648)")
        .expect("two grouped BigRat divisions should combine through bitand");
    BigRat::parse("(error / 658533982) bitand (709677539 / -2024700648) + error")
        .expect("bitand result should continue into plus");
    BigRat::parse("(1578446359 + error) bitand 3521345456")
        .expect("grouped BigRat addition should continue into bitand");
    BigRat::parse("error + (1578446359 + error) bitand 3521345456")
        .expect("plus RHS should preserve a grouped sum continuing into bitand");
    BigRat::parse(
        "(error / 658533982) bitand (709677539 / -2024700648) + \
         (1578446359 + error) bitand 3521345456",
    )
    .expect("BigRat parser should continue grouped error divisions into later infix chains");
}

#[test]
fn calculator_bigrat_grouped_rhs_continues_after_outer_plus() {
    mettail_runtime::clear_var_cache();

    BigRat::parse(
        "(error / 658533982) bitand (709677539 / -2024700648) + \
         (1578446359 + error) bitand 3521345456",
    )
    .expect("outer plus RHS should keep legal higher-precedence BigRat continuations");
}

#[test]
fn calculator_bigrat_projected_prefix_lhs_continues_to_bitand() {
    mettail_runtime::clear_var_cache();

    let input = "bitnot 1131084173p0 bitand \
         (fraction(cast_error_bigint , cast_error_bigint) * -error)";

    BigRat::parse(input).expect("projected prefix LHS should continue into outer BigRat bitand");
}

#[test]
fn calculator_cast_wrapper_surfaces_parse_at_root_categories() {
    mettail_runtime::clear_var_cache();

    Str::parse("str(true)").expect("BoolToStr surface should parse as Str");
    Str::parse("str(cast_error_int)").expect("IntToStr surface should parse as Str");
    Float::parse("float(maplength(map()) != |\"p\"|)")
        .expect("BoolToFloat surface should parse as Float");
    Fixed::parse(
        "fixed(\"\" + \"aztsrrf\" , 1739016572! ? 912726983 : cast_error_int ? error : cast_error_int)",
    )
    .expect("FixedBin surface should parse as Fixed");
    BigRat::parse("bigrat(cast_error_float)").expect("BigratCast surface should parse as BigRat");
}

#[test]
fn calculator_projection_display_canonicalizes_to_parseable_surface() {
    mettail_runtime::clear_var_cache();

    let parsed = BigRat::parse("bigrat(352326912)").expect("BigratCast should admit ProcInt");
    assert_eq!(format!("{}", parsed), "352326912");

    let reparsed = BigRat::parse(&format!("{}", parsed)).expect("canonical BigRat display parses");
    assert_eq!(format!("{}", reparsed), "352326912");

    let lhs = Str::Concat(
        Arc::new(Str::BoolToStr(Arc::new(Bool::BoolLit(true)))),
        Arc::new(Str::StrId(Arc::new(Str::StringLit("z".to_string())))),
    );
    let rhs = Str::Concat(
        Arc::new(Str::StringLit("fbb".to_string())),
        Arc::new(Str::Concat(
            Arc::new(Str::StringLit(String::new())),
            Arc::new(Str::StringLit("fl".to_string())),
        )),
    );
    let bool_display = format!("{}", Bool::LtStr(Arc::new(lhs), Arc::new(rhs)));
    Bool::parse(&bool_display).expect("canonical Bool display parses");
}

#[test]
fn calculator_projection_display_preserves_real_operators() {
    mettail_runtime::clear_var_cache();

    let bigint = BigInt::BitNotBigInt(Arc::new(BigInt::IntToBigInt(Arc::new(
        mettail_languages::calculator::Int::NumLit(971145016),
    ))));
    let bigint_display = format!("{}", bigint);
    assert!(
        bigint_display.starts_with("bitnot "),
        "projection canonicalization must not erase unary BigInt operators: {bigint_display}"
    );
    BigInt::parse(&bigint_display).expect("BigInt unary projection display parses");

    let bigrat = BigRat::NegBigRat(Arc::new(BigRat::IntToBigRat(Arc::new(
        mettail_languages::calculator::Int::NumLit(1191074303),
    ))));
    let bigrat_display = format!("{}", bigrat);
    assert!(
        bigrat_display.starts_with('-'),
        "projection canonicalization must not erase unary BigRat operators: {bigrat_display}"
    );
    BigRat::parse(&bigrat_display).expect("BigRat unary projection display parses");
}

#[test]
fn calculator_syntaxless_projection_surfaces_parse_at_target_root() {
    mettail_runtime::clear_var_cache();

    UInt32::parse("false").expect("BoolToUInt32 should admit Bool literal surface");
    UInt32::parse("false <= true").expect("BoolToUInt32 should admit Bool comparison surface");
    UInt32::parse("(false <= true)").expect("BoolToUInt32 should admit parenthesized Bool surface");
    UInt32::parse("(false <= true) xor (cast_error_float >= cast_error_float)")
        .expect("BoolToUInt32 should admit compound Bool surface");
}

#[test]
fn calculator_bool_chained_projection_surfaces_parse() {
    mettail_runtime::clear_var_cache();

    Bool::parse("816675508 <= cast_error_int")
        .expect("numeric comparison surface should parse as Bool");
    Bool::parse("816675508 <= cast_error_int <= (cast_error_fixed < cast_error_fixed)")
        .expect("Bool comparison over a numeric-comparison LHS should parse");
    Bool::parse(
        "(816675508 <= cast_error_int <= (cast_error_fixed < cast_error_fixed)) \
         != bool(cast_error_float)",
    )
    .expect("parenthesized chained Bool comparison should parse");
}

#[test]
fn calculator_prefix_call_operands_continue_to_infix() {
    mettail_runtime::clear_var_cache();

    mettail_languages::calculator::Int::parse("maplength(map())")
        .expect("LenMap call-style prefix should parse as Int");
    mettail_languages::calculator::Int::parse("int(a , cast_error_int)")
        .expect("IntBin call-style prefix should parse as Int");
    Bool::parse("maplength(map()) != 0")
        .expect("LenMap prefix result should continue to Int comparison");
    Bool::parse("maplength(map()) != int(str(a))")
        .expect("LenMap prefix result should compare against cast-style Int operand");
    Float::parse(
        "0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000065183563307543256",
    )
    .expect("long decimal float literal should parse as Float");
    Bool::parse(
        "bool(0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000065183563307543256)",
    )
    .expect("Bool cast over a long decimal float literal should parse");
}

#[test]
fn calculator_intbin_result_continues_as_bool_chain() {
    mettail_runtime::clear_var_cache();

    Bool::parse("int(a , cast_error_int) > error * error < bool(0.0000000000000001)")
        .expect("IntBin prefix result should continue through chained Bool comparison");
    Bool::parse(
        "int(a , cast_error_int) > error * error < \
         bool(0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000065183563307543256)",
    )
    .expect("IntBin prefix result should not depend on later long float lattice shape");
}

#[test]
fn calculator_string_concatenation_lex_forks_keep_accepting_branch() {
    mettail_runtime::clear_var_cache();

    Str::parse("\"as\" + \"flruphu\" ++ str(\"a\")")
        .expect("mixed +/++ with a syntaxful wrapper RHS should parse");
    Bool::parse("\"a\" < \"b\"").expect("literal string comparison should parse");
    Bool::parse("str(true) < \"fbb\"").expect("cast-wrapper string LHS comparison should parse");
    Bool::parse("str(true) ++ str(\"z\") < \"fbb\"")
        .expect("concatenated string LHS comparison should parse");
    Bool::parse("str(true) < \"fbb\" ++ \"\" ++ \"fl\"")
        .expect("concatenated string RHS comparison should parse");
    Bool::parse("str(true) ++ str(\"z\") < \"fbb\" ++ \"\" ++ \"fl\"")
        .expect("cross-category string comparison should preserve accepting lex branch");
}
