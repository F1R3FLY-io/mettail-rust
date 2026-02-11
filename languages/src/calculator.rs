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
        ![f64] as Float
        ![bool] as Bool
        ![str] as Str
    },
    terms {
        Eq . a:Int, b:Int |- a "==" b : Bool ![a == b] step;
        EqFloat . a:Float, b:Float |- a "==" b : Bool ![a.get() == b.get()] step;
        EqBool . a:Bool, b:Bool |- a "==" b : Bool ![a == b] step;
        EqStr . a:Str, b:Str |- a "==" b : Bool ![a == b] step;
        Not . a:Bool |- "not" a : Bool ![{match a {
            true => false,
            false => true,
        }}] step;
        Pow . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step;
        Comp . a:Bool, b:Bool |- a "&&" b : Bool ![a && b] step;
        Len . s:Str |- "|" s "|" : Int ![s.len() as i32] step;
        Concat . a:Str, b:Str |- a "++" b : Str ![[a, b].concat()] step;
        AddStr . a:Str, b:Str |- a "+" b : Str ![{ let mut x = a.clone(); x.push_str(&b); x }] step;
        Add . a:Int, b:Int |- a "+" b : Int ![a + b] step;
        AddFloat . a:Float, b:Float |- a "+" b : Float ![a + b] step;
        Sub . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
        CustomOp . a:Int, b:Int |- a "~" b : Int ![2 * a + 3 * b] fold;
    },
    equations {
    },
    rewrites {
        AddCongL . | S ~> T |- (Add S R) ~> (Add T R);
        AddCongR . | S ~> T |- (Add L S) ~> (Add L T);
        AddFloatCongL . | S ~> T |- (AddFloat S R) ~> (AddFloat T R);
        AddFloatCongR . | S ~> T |- (AddFloat L S) ~> (AddFloat L T);
        SubCongL . | S ~> T |- (Sub S R) ~> (Sub T R);
        SubCongR . | S ~> T |- (Sub L S) ~> (Sub L T);
        AddStrCongL . | S ~> T |- (AddStr S R) ~> (AddStr T R);
        AddStrCongR . | S ~> T |- (AddStr L S) ~> (AddStr L T);
        CompCongL . | S ~> T |- (Comp S R) ~> (Comp T R);
        CompCongR . | S ~> T |- (Comp L S) ~> (Comp L T);
        NotCong . | S ~> T |- (Not S) ~> (Not T);
        EqCongL . | S ~> T |- (Eq S R) ~> (Eq T R);
        EqCongR . | S ~> T |- (Eq L S) ~> (Eq L T);
        EqFloatCongL . | S ~> T |- (EqFloat S R) ~> (EqFloat T R);
        EqFloatCongR . | S ~> T |- (EqFloat L S) ~> (EqFloat L T);
        EqBoolCongL . | S ~> T |- (EqBool S R) ~> (EqBool T R);
        EqBoolCongR . | S ~> T |- (EqBool L S) ~> (EqBool L T);
        EqStrCongL . | S ~> T |- (EqStr S R) ~> (EqStr T R);
        EqStrCongR . | S ~> T |- (EqStr L S) ~> (EqStr L T);
    },
}
