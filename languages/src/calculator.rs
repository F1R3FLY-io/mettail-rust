#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Calculator,
    types {
        ![i32] as Int
        // Float (f64) omitted: Ascent Datalog requires Eq/Hash on relation types, which f64 does not implement
        ![bool] as Bool
        ![str] as Str
    },
    terms {
        Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int ![{ if c != 0 { t } else { e } }] step right;
        Eq . a:Int, b:Int |- a "==" b : Bool ![a == b] step;
        EqBool . a:Bool, b:Bool |- a "==" b : Bool ![a == b] step;
        EqStr . a:Str, b:Str |- a "==" b : Bool ![a == b] step;
        Not . a:Bool |- "not" a : Bool ![{match a {
            true => false,
            false => true,
        }}] step;
        Pow . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step right;
        Comp . a:Bool, b:Bool |- a "&&" b : Bool ![a && b] step;
        Len . s:Str |- "|" s "|" : Int ![s.len() as i32] step;
        Concat . a:Str, b:Str |- a "++" b : Str ![[a, b].concat()] step;
        AddStr . a:Str, b:Str |- a "+" b : Str ![{ let mut x = a.clone(); x.push_str(&b); x }] step;
        Add . a:Int, b:Int |- a "+" b : Int ![a + b] step;
        Neg . a:Int |- "-" a : Int ![(-a)] fold;
        Sub . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
        CustomOp . a:Int, b:Int |- a "~" b : Int ![2 * a + 3 * b] fold;
        Fact . a:Int |- a "!" : Int ![{ (1..=a.max(0)).product::<i32>() }] step;
    },
    equations {
    },
    rewrites {
        AddCongL . | S ~> T |- (Add S R) ~> (Add T R);
        AddCongR . | S ~> T |- (Add L S) ~> (Add L T);
        NegCong . | S ~> T |- (Neg S) ~> (Neg T);
        SubCongL . | S ~> T |- (Sub S R) ~> (Sub T R);
        SubCongR . | S ~> T |- (Sub L S) ~> (Sub L T);
        AddStrCongL . | S ~> T |- (AddStr S R) ~> (AddStr T R);
        AddStrCongR . | S ~> T |- (AddStr L S) ~> (AddStr L T);
        CompCongL . | S ~> T |- (Comp S R) ~> (Comp T R);
        CompCongR . | S ~> T |- (Comp L S) ~> (Comp L T);
        NotCong . | S ~> T |- (Not S) ~> (Not T);
        EqCongL . | S ~> T |- (Eq S R) ~> (Eq T R);
        EqCongR . | S ~> T |- (Eq L S) ~> (Eq L T);
        EqBoolCongL . | S ~> T |- (EqBool S R) ~> (EqBool T R);
        EqBoolCongR . | S ~> T |- (EqBool L S) ~> (EqBool L T);
        EqStrCongL . | S ~> T |- (EqStr S R) ~> (EqStr T R);
        EqStrCongR . | S ~> T |- (EqStr L S) ~> (EqStr L T);
        FactCong . | S ~> T |- (Fact S) ~> (Fact T);
        TernCongC . | S ~> T |- (Tern S R1 R2) ~> (Tern T R1 R2);
        TernCongT . | S ~> T |- (Tern L S R) ~> (Tern L T R);
        TernCongE . | S ~> T |- (Tern L R S) ~> (Tern L R T);
    },
}
