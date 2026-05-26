// Golden monolithic `language!` body for MyCalc parity (update when `.rho` fixtures change).
pub const SOURCE: &str = r#"
name: MyCalc,
types {
    ![f64] as Float
    ![f64] as Cmplx
},
terms {
    CmplxInj . Cmplx ::= Float ;
    CmplxAdd . Cmplx ::= Cmplx "+" Cmplx ;
}
"#;
