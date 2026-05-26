// Golden monolithic reference for ParMonoid export-rename parity.
pub const SOURCE: &str = r#"
name: ParL,
types {
    Proc
},
terms {
    Zero . Proc ::= "0" ;
}
"#;
