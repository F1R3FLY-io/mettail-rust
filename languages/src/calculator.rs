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
        Comp . a:Bool, b:Bool |- a "&&" b : Bool ![a && b] step;
        Len . s:Str |- "|" s "|" : Int ![s.len() as i32] step;
        AddStr . a:Str, b:Str |- a "+" b : Str ![{ let mut x = a.clone(); x.push_str(&b); x }] step;
        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
        MulInt . a:Int, b:Int |- a "*" b : Int ![a * b] fold;
        DivInt . a:Int, b:Int |- a "/" b : Int ![a / b] fold;
        ModInt . a:Int, b:Int |- a "%" b : Int ![a % b] fold;
        PowInt . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step;

        AddFloat . a:Float, b:Float |- a "+" b : Float ![a + b] fold;
        SubFloat . a:Float, b:Float |- a "-" b : Float ![a - b] fold;
        ToFloat . a:Int |- "float" "(" a ")" : Float ![mettail_runtime::CanonicalFloat64::from(a as f64)] step;
        ToInt . a:Float |- "int" "(" a ")" : Int ![a.get() as i32] step;
        IntId . a:Int |- "int" "(" a ")" : Int ![a] step;
        FloatId . a:Float |- "float" "(" a ")" : Float ![a] step;
        // Example of a custom operation:
        CustomOp . a:Int, b:Int |- a "~" b : Int ![2 * a + 3 * b] fold;
    },
    equations {
    },
    rewrites {
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
        AddIntCongL . | S ~> T |- (AddInt S R) ~> (AddInt T R);
        AddIntCongR . | S ~> T |- (AddInt L S) ~> (AddInt L T);
        SubIntCongL . | S ~> T |- (SubInt S R) ~> (SubInt T R);
        SubIntCongR . | S ~> T |- (SubInt L S) ~> (SubInt L T);
        MulIntCongL . | S ~> T |- (MulInt S R) ~> (MulInt T R);
        MulIntCongR . | S ~> T |- (MulInt L S) ~> (MulInt L T);
        DivIntCongL . | S ~> T |- (DivInt S R) ~> (DivInt T R);
        DivIntCongR . | S ~> T |- (DivInt L S) ~> (DivInt L T);
        ModIntCongL . | S ~> T |- (ModInt S R) ~> (ModInt T R);
        ModIntCongR . | S ~> T |- (ModInt L S) ~> (ModInt L T);
        PowIntCongL . | S ~> T |- (PowInt S R) ~> (PowInt T R);
        
        AddFloatCongL . | S ~> T |- (AddFloat S R) ~> (AddFloat T R);
        AddFloatCongR . | S ~> T |- (AddFloat L S) ~> (AddFloat L T);
        SubFloatCongL . | S ~> T |- (SubFloat S R) ~> (SubFloat T R);
        SubFloatCongR . | S ~> T |- (SubFloat L S) ~> (SubFloat L T);
        ToFloatCong . | S ~> T |- (ToFloat S) ~> (ToFloat T);
        ToIntCong . | S ~> T |- (ToInt S) ~> (ToInt T);
        IntIdCong . | S ~> T |- (IntId S) ~> (IntId T);
        FloatIdCong . | S ~> T |- (FloatId S) ~> (FloatId T);
    },
}
