//! M-RHO.0.5 / M-RHO.0.4: run the lowered calculator scalar-op contracts on a
//! REAL in-memory f1r3node-rust `RhoRuntime` and assert the computed results.
//!
//! For each Int operator the lowered Rholang contract (from
//! `mettail_rho_codegen::lower_language_def`) is installed, called with concrete
//! arguments, and the result read back from a fixed output channel. The asserted
//! values ARE the calculator's defined arithmetic semantics (`AddInt = a + b`,
//! …) — i.e. exactly what the Ascent backend computes — so this is the per-op
//! differential oracle (rho-backend ≡ Ascent) executed end-to-end.

use mettail_ast::language::LanguageDef;
use mettail_rho_codegen::lower_language_def;
use mettail_rho_runtime::run_and_read_ints;

// The calculator's Int scalar-op fragment, body-less (the lowering keys on the
// concrete-syntax operator + operand types). Every rule here lowers to a Rholang
// contract.
const CALC_RUN_FRAGMENT: &str = r#"
    name: CalcRun,
    types { Proc }
    terms {
        AddInt . a:Int, b:Int |- a "+" b : Int ;
        SubInt . a:Int, b:Int |- a "-" b : Int ;
        MulInt . a:Int, b:Int |- a "*" b : Int ;
        DivInt . a:Int, b:Int |- a "/" b : Int ;
        ModInt . a:Int, b:Int |- a "%" b : Int ;
        Neg . a:Int |- "-" a : Int ;
    }
"#;

fn calculator_contracts() -> String {
    let def =
        syn::parse_str::<LanguageDef>(CALC_RUN_FRAGMENT).expect("calculator fragment must parse");
    let lowering = lower_language_def(&def);
    assert_eq!(
        lowering.lowered,
        vec!["AddInt", "SubInt", "MulInt", "DivInt", "ModInt", "Neg"],
        "all six Int scalar ops must lower"
    );
    assert!(lowering.rejected.is_empty(), "no rule should be rejected here");
    lowering.source
}

/// `new ret in { <contracts> | @"OP"!(a, b, *ret) | for (@v <- ret) { @"OUT"!(v) } }`
fn binary_program(contracts: &str, op: &str, a: i64, b: i64) -> String {
    format!(
        "new ret in {{\n{contracts} |\n@\"{op}\"!({a}, {b}, *ret) |\nfor (@v <- ret) {{ @\"OUT\"!(v) }}\n}}"
    )
}

/// `new ret in { <contracts> | @"OP"!(a, *ret) | for (@v <- ret) { @"OUT"!(v) } }`
fn unary_program(contracts: &str, op: &str, a: i64) -> String {
    format!(
        "new ret in {{\n{contracts} |\n@\"{op}\"!({a}, *ret) |\nfor (@v <- ret) {{ @\"OUT\"!(v) }}\n}}"
    )
}

#[tokio::test]
async fn lowered_calculator_int_ops_compute_correctly_on_rho_runtime() {
    let contracts = calculator_contracts();

    let cases: &[(&str, i64, i64, i64)] = &[
        ("AddInt", 2, 3, 5),
        ("SubInt", 10, 4, 6),
        ("MulInt", 3, 7, 21),
        ("DivInt", 20, 4, 5),
        ("ModInt", 17, 5, 2),
    ];
    for &(op, a, b, expected) in cases {
        let program = binary_program(&contracts, op, a, b);
        let result = run_and_read_ints(&program, "OUT")
            .await
            .unwrap_or_else(|e| panic!("{op}({a},{b}) failed to run: {e}"));
        assert_eq!(result, vec![expected], "{op}({a}, {b}) on RhoRuntime");
    }

    // Unary negation.
    let program = unary_program(&contracts, "Neg", 7);
    let result = run_and_read_ints(&program, "OUT")
        .await
        .unwrap_or_else(|e| panic!("Neg(7) failed to run: {e}"));
    assert_eq!(result, vec![-7], "Neg(7) on RhoRuntime");
}
