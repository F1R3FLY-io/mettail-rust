//! M-RHO.0.4: the differential oracle, executed against BOTH real backends.
//!
//! For each calculator Int operation this runs:
//!   - the ASCENT backend: `CalculatorLanguage::run_ascent(parse_term(input))` →
//!     its normal-form display strings, and
//!   - the RHO backend: the lowered Rholang contract (mettail-rho-codegen) on a
//!     real in-memory f1r3node RhoRuntime (mettail-rho-runtime),
//! and asserts the rho result is among the Ascent normal forms (weight-erased =
//! display-string comparison). This is the genuine two-backend differential the
//! exactness proof `OracleQuotientEquivalence.v` underwrites — not a comparison
//! against hand-written constants.

use mettail_ast::language::LanguageDef;
use mettail_languages::calculator::CalculatorLanguage;
use mettail_rho_codegen::lower_language_def;
use mettail_rho_runtime::run_and_read_ints;
use mettail_runtime::Language;

const CALC_RUN_FRAGMENT: &str = r#"
    name: CalcRun,
    types { Proc }
    terms {
        AddInt . a:Int, b:Int |- a "+" b : Int ;
        SubInt . a:Int, b:Int |- a "-" b : Int ;
        MulInt . a:Int, b:Int |- a "*" b : Int ;
        DivInt . a:Int, b:Int |- a "/" b : Int ;
        ModInt . a:Int, b:Int |- a "%" b : Int ;
    }
"#;

fn calculator_contracts() -> String {
    let def =
        syn::parse_str::<LanguageDef>(CALC_RUN_FRAGMENT).expect("calculator fragment must parse");
    lower_language_def(&def).source
}

/// The Ascent backend's normal-form display strings for `input`.
fn ascent_normal_forms(lang: &CalculatorLanguage, input: &str) -> Vec<String> {
    let parsed = lang.parse_term(input).expect("calculator parse");
    let results = lang.run_ascent(parsed.as_ref()).expect("ascent eval");
    results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect()
}

/// The rho backend's result of `@"op"(a, b)` on a real RhoRuntime.
async fn rho_binary(contracts: &str, op: &str, a: i64, b: i64) -> i64 {
    let program = format!(
        "new ret in {{\n{contracts} |\n@\"{op}\"!({a}, {b}, *ret) |\nfor (@v <- ret) {{ @\"OUT\"!(v) }}\n}}"
    );
    let result = run_and_read_ints(&program, "OUT")
        .await
        .unwrap_or_else(|e| panic!("rho {op}({a},{b}): {e}"));
    assert_eq!(result.len(), 1, "rho {op}({a},{b}) must yield exactly one int");
    result[0]
}

#[tokio::test]
async fn rho_backend_agrees_with_ascent_on_calculator_int_ops() {
    let lang = CalculatorLanguage;
    let contracts = calculator_contracts();

    // (Ascent input string, rho op label, operands). The calculator parses the
    // input to the matching constructor; both backends must agree on the result.
    let cases: &[(&str, &str, i64, i64)] = &[
        ("2 + 3", "AddInt", 2, 3),
        ("10 - 4", "SubInt", 10, 4),
        ("3 * 7", "MulInt", 3, 7),
        ("20 / 4", "DivInt", 20, 4),
        ("17 % 5", "ModInt", 17, 5),
    ];

    for &(input, op, a, b) in cases {
        let ascent = ascent_normal_forms(&lang, input);
        let rho = rho_binary(&contracts, op, a, b).await;
        assert!(
            ascent.contains(&rho.to_string()),
            "DIVERGENCE on `{input}`: rho-backend = {rho}, Ascent normal forms = {ascent:?}"
        );
    }
}
