use mettail_languages::calculator::{BigInt, BigRat, Bool, Fixed, Float, Int, Proc, Str, UInt32};
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
fn calculator_bigrat_bitand_bitor_canonical_display_is_idempotent() {
    mettail_runtime::clear_var_cache();

    let term = BigRat::BitAndBigRat(
        Arc::new(BigRat::BitOrBigRat(
            Arc::new(BigRat::BitOrBigRat(
                Arc::new(BigRat::IntToBigRat(Arc::new(
                    mettail_languages::calculator::Int::NumLit(-1431143609),
                ))),
                Arc::new(BigRat::Err),
            )),
            Arc::new(BigRat::DivBigRat(
                Arc::new(BigRat::IntToBigRat(Arc::new(
                    mettail_languages::calculator::Int::NumLit(777437875),
                ))),
                Arc::new(BigRat::Err),
            )),
        )),
        Arc::new(BigRat::BigratCast(Arc::new(Proc::ProcFloat(Arc::new(Float::CastErrFloat))))),
    );

    let displayed = format!("{}", term);
    let parsed = BigRat::parse(&displayed).expect("displayed BigRat should parse");
    let canonical = format!("{}", parsed);
    let reparsed = BigRat::parse(&canonical).expect("canonical BigRat display should parse");
    let recanonical = format!("{}", reparsed);

    assert_eq!(
        canonical, recanonical,
        "canonical BigRat display must be stable after parsing; displayed={displayed:?}"
    );
}

#[test]
fn calculator_bigrat_int_projection_add_display_is_idempotent() {
    mettail_runtime::clear_var_cache();

    let term = BigRat::AddBigRat(
        Arc::new(BigRat::IntToBigRat(Arc::new(Int::AddInt(
            Arc::new(Int::NumLit(353703189)),
            Arc::new(Int::NumLit(353703189)),
        )))),
        Arc::new(BigRat::Err),
    );

    let displayed = format!("{}", term);
    assert!(
        displayed.contains("bigrat("),
        "cross-category projection used as an operand should preserve its source syntax with an explicit wrapper: {displayed:?}"
    );

    let parsed = BigRat::parse(&displayed).expect("displayed BigRat should parse");
    let canonical = format!("{}", parsed);
    let reparsed = BigRat::parse(&canonical).expect("canonical BigRat display should parse");
    let recanonical = format!("{}", reparsed);

    assert_eq!(
        canonical, recanonical,
        "canonical BigRat display must be stable after parsing; displayed={displayed:?}"
    );
}

#[test]
fn calculator_proc_bigrat_bit_or_add_display_is_idempotent() {
    mettail_runtime::clear_var_cache();

    let term = Proc::ProcBigRat(Arc::new(BigRat::AddBigRat(
        Arc::new(BigRat::BitOrBigRat(Arc::new(BigRat::Err), Arc::new(BigRat::Err))),
        Arc::new(BigRat::AddBigRat(
            Arc::new(BigRat::RatLit(mettail_runtime::CanonicalBigRat::from(
                num_rational::Ratio::from_integer(num_bigint::BigInt::from(-719987712)),
            ))),
            Arc::new(BigRat::Err),
        )),
    )));

    let displayed = format!("{}", term);
    let parsed = Proc::parse(&displayed).expect("displayed Proc should parse");
    let canonical = format!("{}", parsed);
    let reparsed = Proc::parse(&canonical).expect("canonical Proc display should parse");
    let recanonical = format!("{}", reparsed);

    assert_eq!(
        canonical, recanonical,
        "canonical Proc display must be stable after parsing; displayed={displayed:?}"
    );
}

#[test]
fn calculator_bigrat_projected_integer_add_tree_keeps_surface_representative() {
    mettail_runtime::clear_var_cache();

    let input = "353703189 + 353703189 + (353703189 + 353703189) + \
                 (353703189 + 353703189 + (353703189 + 353703189))";

    let parsed = BigRat::parse(input).expect("ambiguous integer BigRat addition tree should parse");
    let canonical = format!("{}", parsed);

    let reparsed = BigRat::parse(&canonical).expect("canonical BigRat display should parse again");
    assert_eq!(
        format!("{}", reparsed),
        canonical,
        "single-result parsing should converge to a stable display representative from input={input:?}"
    );
}

#[test]
fn calculator_str_cast_nested_bool_comparison_parses_without_snapshot_overflow() {
    mettail_runtime::clear_var_cache();

    let input = "str(0 + error != int(0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000566938))";
    Str::parse(input).expect("displayed Str cast over an ambiguous Bool should parse");
}

#[test]
fn calculator_proc_fixed_comparison_parses_without_snapshot_overflow() {
    mettail_runtime::clear_var_cache();

    let input = "cast_error_fixed + cast_error_fixed > 508886636p0 bitor 1425960177p0";
    Proc::parse(input).expect("displayed Proc comparison over Fixed operators should parse");
}

#[test]
fn calculator_float_cast_parenthesized_prefix_operand_parses() {
    mettail_runtime::clear_var_cache();

    let input = "float(-(1.0 + cast_error_float))";
    let parsed = Float::parse(input).expect("FloatId should parse a grouped NegFloat operand");
    assert_eq!(format!("{}", parsed), input);
}

#[test]
fn calculator_float_infix_rhs_keeps_prefix_operand_path() {
    mettail_runtime::clear_var_cache();

    let input = "float(a , 1) ^ -1.0 * (cast_error_float ^ 0.1 * cast_error_float)";
    let parsed = Float::parse(input).expect("Float infix RHS should admit prefix negation");
    assert_eq!(format!("{}", parsed), input);
}

#[test]
fn calculator_same_category_cast_body_waits_for_infix_completion() {
    mettail_runtime::clear_var_cache();

    BigRat::parse("bigrat(error) + (error + error)")
        .expect("BigratCast body completion must not hide the outer BigRat infix");
    Proc::parse("bigrat(error) + (error + error)")
        .expect("ProcBigRat display should preserve the same complete BigRat parse path");
}

#[test]
fn calculator_bool_cast_and_comparison_chains_keep_later_infix() {
    mettail_runtime::clear_var_cache();

    Bool::parse("(bool(0.0000000000000001) > (false == false)) >= |\"whbaaa\"| >= error")
        .expect("Bool cast/comparison chains should retain later Bool continuations");
}

#[test]
fn calculator_bigrat_infix_rhs_keeps_prefix_operand_path() {
    mettail_runtime::clear_var_cache();

    BigRat::parse("bigrat(160208597) / -error")
        .expect("BigRat infix RHS should admit prefix negation over Err");
}

#[test]
fn calculator_prefix_cast_wrap_restores_enclosing_prefix_floor() {
    mettail_runtime::clear_var_cache();

    let input = "bitnot bigrat(0 bitand -1142617375) + error";
    let parsed = BigRat::parse(input).expect("prefix cast operand should parse");
    let canonical = format!("{}", parsed);
    assert_eq!(
        canonical, input,
        "trailing lower-precedence infix must stay outside the prefix operand"
    );

    let reparsed = BigRat::parse(&canonical).expect("canonical BigRat display should parse");
    assert_eq!(
        format!("{}", reparsed),
        canonical,
        "prefix/cast display should remain stable after a second parse"
    );
}

#[test]
fn calculator_prefix_syntaxless_projection_restores_enclosing_prefix_floor() {
    mettail_runtime::clear_var_cache();

    let input = "bitnot 541791495 + bitnot 899164433";
    let raw = BigRat::parse_via_wpda(input).expect("raw WPDA prefix projection should parse");
    let raw_display = format!("{}", raw);
    let expected = "bitnot bigrat(541791495) + bitnot bigrat(899164433)";
    assert_eq!(
        raw_display, expected,
        "raw WPDA parse should preserve the prefix operand floor before representative stabilization"
    );
    let parsed = BigRat::parse(input).expect("prefix projection operand should parse");
    let canonical = format!("{}", parsed);
    assert_eq!(
        canonical, expected,
        "syntaxless projection must preserve the prefix operand floor so + stays outside while \
         retaining contextual projection wrappers"
    );

    let reparsed = BigRat::parse(&canonical).expect("canonical BigRat display should parse");
    assert_eq!(
        format!("{}", reparsed),
        canonical,
        "syntaxless projection display should remain stable after a second parse"
    );
}

#[test]
fn calculator_uint32_bool_projection_keeps_source_comparison() {
    mettail_runtime::clear_var_cache();

    let input = "bitnot 840384306 < bitnot 840384306";
    let parsed = UInt32::parse(input)
        .expect("UInt32 syntaxless Bool projection should keep the Int comparison path");
    assert_eq!(
        format!("{}", parsed),
        input,
        "BoolToUInt32 over an Int comparison must remain parseable from its surface display"
    );
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
fn calculator_projection_display_distinguishes_casts_from_syntaxless_injections() {
    mettail_runtime::clear_var_cache();

    let parsed = BigRat::parse("bigrat(352326912)").expect("BigratCast should admit ProcInt");
    assert_eq!(format!("{}", parsed), "bigrat(352326912)");

    let reparsed = BigRat::parse(&format!("{}", parsed)).expect("canonical BigRat display parses");
    assert_eq!(format!("{}", reparsed), "bigrat(352326912)");

    let syntaxless_projection =
        BigRat::IntToBigRat(Arc::new(mettail_languages::calculator::Int::NumLit(352326912)));
    let projected_display = format!("{}", syntaxless_projection);
    assert_eq!(projected_display, "352326912");
    let reparsed_projection =
        BigRat::parse(&projected_display).expect("syntaxless BigRat display parses");
    assert_eq!(format!("{}", reparsed_projection), "352326912");

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
fn calculator_bool_source_body_exits_resume_bool_continuation() {
    mettail_runtime::clear_var_cache();

    Bool::parse(
        "(true and false > error != cast_error_int) <= \
         (str(cast_error_float) <= str(cast_error_float))",
    )
    .expect("source-body category exit should resume the produced Bool continuation");
    Bool::parse("(false <= false == 24835 != cast_error_int) < ((true == false) < false)")
        .expect("grouped Bool chains should preserve source-exit ambiguity");
}

#[test]
fn calculator_bool_source_body_exits_minimal_chain() {
    mettail_runtime::clear_var_cache();

    Bool::parse("false > (error != cast_error_int)")
        .expect("Bool comparison RHS should admit a produced Bool from a source comparison");
    Bool::parse("false > error != cast_error_int")
        .expect("ambiguous Bool/source comparison chain should keep the produced Bool RHS");
}

#[test]
fn calculator_nextest_property_counterexamples_parse() {
    mettail_runtime::clear_var_cache();

    Proc::parse("(2037137192p0 - cast_error_fixed) % -1697949250p0 bitand cast_error_fixed")
        .expect("Proc should admit projected Fixed bitwise/modulo chains");
    BigRat::parse(
        "-886879249 + (error + 213439954) bitand \
         fraction(-222099783 , cast_error_bigint)",
    )
    .expect("BigRat should continue through prefix RHS after bitand");
    BigInt::parse("(cast_error_float < cast_error_float) <= \"skdkxs\" != \"gr\"")
        .expect("BigInt should admit chained Bool surfaces");
    Bool::parse("error ~ error - int(a , error) != |\"ve\"| % cast_error_int!")
        .expect("Bool should admit arithmetic RHS with postfix factorial");
    Float::parse("float(cast_error_int != error , count(bag() , -318922039))")
        .expect("Float should admit call-style operands with nested Bool/Bag evidence");
    Str::parse("\"as\" + \"flruphu\" ++ str(a) ++ (str(a) ++ (\"i\" ++ \"as\"))")
        .expect("Str should continue through mixed +/++ and prefix casts");
}

#[test]
fn calculator_infix_rhs_keeps_function_prefix_atoms() {
    mettail_runtime::clear_var_cache();

    let str_term = Str::AddStr(
        Arc::new(Str::AddStr(
            Arc::new(Str::StringLit("a".to_string())),
            Arc::new(Str::Concat(
                Arc::new(Str::StringLit("daecaba".to_string())),
                Arc::new(Str::StringLit("x".to_string())),
            )),
        )),
        Arc::new(Str::BoolToStr(Arc::new(Bool::BoolLit(false)))),
    );
    let str_display = format!("{}", str_term);
    let parsed_str = Str::parse(&str_display)
        .unwrap_or_else(|err| panic!("displayed Str should parse: {str_display:?}: {err}"));
    assert_eq!(format!("{}", parsed_str), str_display);

    let proc_term = Proc::ProcStr(Arc::new(Str::AddStr(
        Arc::new(Str::AddStr(
            Arc::new(Str::StringLit("aa".to_string())),
            Arc::new(Str::StringLit("eackaa".to_string())),
        )),
        Arc::new(Str::StrId(Arc::new(Str::StringLit("acka".to_string())))),
    )));
    let proc_display = format!("{}", proc_term);
    let parsed_proc = Proc::parse(&proc_display)
        .unwrap_or_else(|err| panic!("displayed Proc should parse: {proc_display:?}: {err}"));
    assert_eq!(format!("{}", parsed_proc), proc_display);
}

#[test]
fn calculator_bool_rhs_keeps_cross_category_comparison_atoms() {
    mettail_runtime::clear_var_cache();

    let term = Bool::EqBool(
        Arc::new(Bool::And(
            Arc::new(Bool::EqFloat(
                Arc::new(Float::CastErrFloat),
                Arc::new(Float::FloatLit(0.0.into())),
            )),
            Arc::new(Bool::NeFloat(Arc::new(Float::CastErrFloat), Arc::new(Float::CastErrFloat))),
        )),
        Arc::new(Bool::GtStr(
            Arc::new(Str::BoolToStr(Arc::new(Bool::BoolLit(false)))),
            Arc::new(Str::StringLit(String::new())),
        )),
    );
    let displayed = format!("{}", term);
    let parsed = Bool::parse(&displayed)
        .unwrap_or_else(|err| panic!("displayed Bool should parse: {displayed:?}: {err}"));
    assert_eq!(format!("{}", parsed), displayed);
}

#[test]
fn calculator_bigint_grouped_infix_cast_rhs_display_parses() {
    mettail_runtime::clear_var_cache();

    let cast = BigInt::BigintCast(Arc::new(Proc::ProcBigInt(Arc::new(BigInt::CastErrBigInt))));
    let term = BigInt::BitAndBigInt(
        Arc::new(BigInt::BitAndBigInt(Arc::new(BigInt::CastErrBigInt), Arc::new(cast))),
        Arc::new(BigInt::CastErrBigInt),
    );
    let displayed = format!("{}", term);
    let parsed = BigInt::parse(&displayed)
        .unwrap_or_else(|err| panic!("displayed BigInt should parse: {displayed:?}: {err}"));
    assert_eq!(format!("{}", parsed), displayed);
}

#[test]
fn calculator_int_cast_surface_admits_int_addition_operand() {
    mettail_runtime::clear_var_cache();

    Int::parse("int(error + error)").expect("Int cast surface should admit Int addition operands");
}

#[test]
fn calculator_bigint_syntaxless_projection_admits_int_cast_surface() {
    mettail_runtime::clear_var_cache();

    BigInt::parse("int(error + error)")
        .expect("BigInt syntaxless IntToBigInt projection should admit Int cast surfaces");
}

#[test]
fn calculator_uint32_display_groups_transparent_bool_operand() {
    mettail_runtime::clear_var_cache();

    let term = UInt32::BitAndUInt32(
        Arc::new(UInt32::BoolToUInt32(Arc::new(Bool::LtEqInt(
            Arc::new(mettail_languages::calculator::Int::NumLit(816675508)),
            Arc::new(mettail_languages::calculator::Int::CastErrInt),
        )))),
        Arc::new(UInt32::BitOrUInt32(
            Arc::new(UInt32::BitAndUInt32(
                Arc::new(UInt32::CastErrUInt32),
                Arc::new(UInt32::CastErrUInt32),
            )),
            Arc::new(UInt32::NumLit(3428493361)),
        )),
    );

    let displayed = format!("{}", term);
    assert!(
        displayed.starts_with("(816675508 <= cast_error_int) bitand "),
        "transparent BoolToUInt32 operands must be grouped before UInt32 bitwise \
         continuations; displayed={displayed:?}"
    );

    let parsed = UInt32::parse(&displayed).expect("displayed UInt32 should parse");
    let canonical = format!("{}", parsed);
    let reparsed = UInt32::parse(&canonical).expect("canonical UInt32 display should parse");
    assert_eq!(
        canonical,
        format!("{}", reparsed),
        "canonical UInt32 display must remain parse-stable"
    );
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

#[test]
fn calculator_string_cast_wrapped_source_comparisons_parse() {
    mettail_runtime::clear_var_cache();

    let cast_wrapped_sources = &[
        "str(cast_error_float * cast_error_float) > str(error == error)",
        "str(error == error) < str(error != error)",
        "str(cast_error_float * cast_error_float) <= str(cast_error_float + cast_error_float)",
    ];
    for input in cast_wrapped_sources {
        Bool::parse(input).unwrap_or_else(|e| {
            panic!("string comparison should preserve cast-wrapped source operand {input:?}: {e:?}")
        });
    }
}
