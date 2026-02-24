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
        // Ternary conditional (right-associative so a ? b : c ? d : e = a ? b : (c ? d : e))
        Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int ![{ if c != 0 { t } else { e } }] step right;
        // Comparison operations
        EqInt . a:Int, b:Int |- a "==" b : Bool ![a == b] step;
        EqFloat . a:Float, b:Float |- a "==" b : Bool ![a == b] step;
        EqBool . a:Bool, b:Bool |- a "==" b : Bool ![a == b] step;
        EqStr . a:Str, b:Str |- a "==" b : Bool ![a == b] step;
        GtInt . a:Int, b:Int |- a ">" b : Bool ![a > b] step;
        GtFloat . a:Float, b:Float |- a ">" b : Bool ![a > b] step;
        GtBool . a:Bool, b:Bool |- a ">" b : Bool ![a & !b] step;
        GtStr . a:Str, b:Str |- a ">" b : Bool ![a > b] step;
        LtInt . a:Int, b:Int |- a "<" b : Bool ![a < b] step;
        LtFloat . a:Float, b:Float |- a "<" b : Bool ![a < b] step;
        LtBool . a:Bool, b:Bool |- a "<" b : Bool ![!a & b] step;
        LtStr . a:Str, b:Str |- a "<" b : Bool ![a < b] step;
        LtEqInt . a:Int, b:Int |- a "<=" b : Bool ![a <= b] step;
        LtEqFloat . a:Float, b:Float |- a "<=" b : Bool ![a <= b] step;
        LtEqBool . a:Bool, b:Bool |- a "<=" b : Bool ![a <= b] step;
        LtEqStr . a:Str, b:Str |- a "<=" b : Bool ![a <= b] step;
        GtEqInt . a:Int, b:Int |- a ">=" b : Bool ![a >= b] step;
        GtEqFloat . a:Float, b:Float |- a ">=" b : Bool ![a >= b] step;
        GtEqBool . a:Bool, b:Bool |- a ">=" b : Bool ![a >= b] step;
        GtEqStr . a:Str, b:Str |- a ">=" b : Bool ![a >= b] step;
        NeInt . a:Int, b:Int |- a "!=" b : Bool ![a != b] step;
        NeFloat . a:Float, b:Float |- a "!=" b : Bool ![a != b] step;
        NeBool . a:Bool, b:Bool |- a "!=" b : Bool ![a != b] step;
        NeStr . a:Str, b:Str |- a "!=" b : Bool ![a != b] step;
        // Boolean operations
        Not . a:Bool |- "not" a : Bool ![{match a {
            true => false,
            false => true,
        }}] step;
        And . a:Bool, b:Bool |- a "and" b : Bool ![a && b] step;
        Or . a:Bool, b:Bool |- a "or" b : Bool ![a || b] step;
        Xor . a:Bool, b:Bool |- a "xor" b : Bool ![a ^ b] step;
        // String operations
        Len . s:Str |- "|" s "|" : Int ![s.len() as i32] step;
        Concat . a:Str, b:Str |- a "++" b : Str ![[a, b].concat()] step;
        AddStr . a:Str, b:Str |- a "+" b : Str ![{ let mut x = a.clone(); x.push_str(&b); x }] step;
        // Int operations
        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
        MulInt . a:Int, b:Int |- a "*" b : Int ![a * b] fold;
        DivInt . a:Int, b:Int |- a "/" b : Int ![a / b] fold;
        ModInt . a:Int, b:Int |- a "%" b : Int ![a % b] fold;
        PowInt . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step right;
        Neg . a:Int |- "-" a : Int ![(-a)] fold;
        Fact . a:Int |- a "!" : Int ![{ (1..=a.max(0)).product::<i32>() }] step;
        // Float operations
        AddFloat . a:Float, b:Float |- a "+" b : Float ![a + b] fold;
        SubFloat . a:Float, b:Float |- a "-" b : Float ![a - b] fold;
        MulFloat . a:Float, b:Float |- a "*" b : Float ![a * b] fold;
        DivFloat . a:Float, b:Float |- a "/" b : Float ![a / b] fold;
        PowFloat . a:Float, b:Float |- a "^" b : Float ![a.powf(b)] step right;
        SinFloat . a:Float |- "sin" "(" a ")" : Float ![a.sin()] step;
        CosFloat . a:Float |- "cos" "(" a ")" : Float ![a.cos()] step;
        ExpFloat . a:Float |- "exp" "(" a ")" : Float ![a.exp()] step;
        LnFloat . a:Float |- "ln" "(" a ")" : Float ![a.ln()] step;
        // Type casts
        IntToFloat . a:Int |- "float" "(" a ")" : Float ![mettail_runtime::CanonicalFloat64::from(a as f64)] step;
        BoolToFloat . a:Bool |- "float" "(" a ")" : Float ![mettail_runtime::CanonicalFloat64::from(if a { 1.0 } else { 0.0 })] step;
        StrToFloat . a:Str |- "float" "(" a ")" : Float ![mettail_runtime::CanonicalFloat64::from(a.parse().unwrap_or(0.0))] step;
        FloatToInt . a:Float |- "int" "(" a ")" : Int ![a.get() as i32] step;
        BoolToInt . a:Bool |- "int" "(" a ")" : Int ![if a { 1 } else { 0 }] step;
        StrToInt . a:Str |- "int" "(" a ")" : Int ![a.parse().unwrap_or(0)] step;
        BoolToStr . a:Bool |- "str" "(" a ")" : Str ![a.to_string()] step;
        IntToStr . a:Int |- "str" "(" a ")" : Str ![a.to_string()] step;
        FloatToStr . a:Float |- "str" "(" a ")" : Str ![a.to_string()] step;
        IntToBool . a:Int |- "bool" "(" a ")" : Bool ![a != 0] step;
        FloatToBool . a:Float |- "bool" "(" a ")" : Bool ![a.get() != 0.0] step;
        StrToBool . a:Str |- "bool" "(" a ")" : Bool ![a.parse().unwrap_or(false)] step;
        IntId . a:Int |- "int" "(" a ")" : Int ![a] step;
        FloatId . a:Float |- "float" "(" a ")" : Float ![a] step;
        BoolId . a:Bool |- "bool" "(" a ")" : Bool ![a] step;
        StrId . a:Str |- "str" "(" a ")" : Str ![a] step;
        // Custom operation (PraTTaIL test feature)
        CustomOp . a:Int, b:Int |- a "~" b : Int ![2 * a + 3 * b] fold;
    },
    equations {
    },
    rewrites {
        // Comparison operations
        EqIntCongL . | S ~> T |- (EqInt S R) ~> (EqInt T R);
        EqIntCongR . | S ~> T |- (EqInt L S) ~> (EqInt L T);
        EqFloatCongL . | S ~> T |- (EqFloat S R) ~> (EqFloat T R);
        EqFloatCongR . | S ~> T |- (EqFloat L S) ~> (EqFloat L T);
        EqBoolCongL . | S ~> T |- (EqBool S R) ~> (EqBool T R);
        EqBoolCongR . | S ~> T |- (EqBool L S) ~> (EqBool L T);
        EqStrCongL . | S ~> T |- (EqStr S R) ~> (EqStr T R);
        EqStrCongR . | S ~> T |- (EqStr L S) ~> (EqStr L T);
        GtIntCongL . | S ~> T |- (GtInt S R) ~> (GtInt T R);
        GtIntCongR . | S ~> T |- (GtInt L S) ~> (GtInt L T);
        GtFloatCongL . | S ~> T |- (GtFloat S R) ~> (GtFloat T R);
        GtFloatCongR . | S ~> T |- (GtFloat L S) ~> (GtFloat L T);
        GtBoolCongL . | S ~> T |- (GtBool S R) ~> (GtBool T R);
        GtBoolCongR . | S ~> T |- (GtBool L S) ~> (GtBool L T);
        GtStrCongL . | S ~> T |- (GtStr S R) ~> (GtStr T R);
        GtStrCongR . | S ~> T |- (GtStr L S) ~> (GtStr L T);
        LtIntCongL . | S ~> T |- (LtInt S R) ~> (LtInt T R);
        LtIntCongR . | S ~> T |- (LtInt L S) ~> (LtInt L T);
        LtFloatCongL . | S ~> T |- (LtFloat S R) ~> (LtFloat T R);
        LtFloatCongR . | S ~> T |- (LtFloat L S) ~> (LtFloat L T);
        LtBoolCongL . | S ~> T |- (LtBool S R) ~> (LtBool T R);
        LtBoolCongR . | S ~> T |- (LtBool L S) ~> (LtBool L T);
        LtStrCongL . | S ~> T |- (LtStr S R) ~> (LtStr T R);
        LtStrCongR . | S ~> T |- (LtStr L S) ~> (LtStr L T);
        LtEqIntCongL . | S ~> T |- (LtEqInt S R) ~> (LtEqInt T R);
        LtEqIntCongR . | S ~> T |- (LtEqInt L S) ~> (LtEqInt L T);
        LtEqFloatCongL . | S ~> T |- (LtEqFloat S R) ~> (LtEqFloat T R);
        LtEqFloatCongR . | S ~> T |- (LtEqFloat L S) ~> (LtEqFloat L T);
        LtEqBoolCongL . | S ~> T |- (LtEqBool S R) ~> (LtEqBool T R);
        LtEqBoolCongR . | S ~> T |- (LtEqBool L S) ~> (LtEqBool L T);
        LtEqStrCongL . | S ~> T |- (LtEqStr S R) ~> (LtEqStr T R);
        LtEqStrCongR . | S ~> T |- (LtEqStr L S) ~> (LtEqStr L T);
        GtEqIntCongL . | S ~> T |- (GtEqInt S R) ~> (GtEqInt T R);
        GtEqIntCongR . | S ~> T |- (GtEqInt L S) ~> (GtEqInt L T);
        GtEqFloatCongL . | S ~> T |- (GtEqFloat S R) ~> (GtEqFloat T R);
        GtEqFloatCongR . | S ~> T |- (GtEqFloat L S) ~> (GtEqFloat L T);
        GtEqBoolCongL . | S ~> T |- (GtEqBool S R) ~> (GtEqBool T R);
        GtEqBoolCongR . | S ~> T |- (GtEqBool L S) ~> (GtEqBool L T);
        GtEqStrCongL . | S ~> T |- (GtEqStr S R) ~> (GtEqStr T R);
        GtEqStrCongR . | S ~> T |- (GtEqStr L S) ~> (GtEqStr L T);
        NeIntCongL . | S ~> T |- (NeInt S R) ~> (NeInt T R);
        NeIntCongR . | S ~> T |- (NeInt L S) ~> (NeInt L T);
        NeFloatCongL . | S ~> T |- (NeFloat S R) ~> (NeFloat T R);
        NeFloatCongR . | S ~> T |- (NeFloat L S) ~> (NeFloat L T);
        NeBoolCongL . | S ~> T |- (NeBool S R) ~> (NeBool T R);
        NeBoolCongR . | S ~> T |- (NeBool L S) ~> (NeBool L T);
        NeStrCongL . | S ~> T |- (NeStr S R) ~> (NeStr T R);
        NeStrCongR . | S ~> T |- (NeStr L S) ~> (NeStr L T);
        // Boolean operations
        AndCongL . | S ~> T |- (And S R) ~> (And T R);
        AndCongR . | S ~> T |- (And L S) ~> (And L T);
        OrCongL . | S ~> T |- (Or S R) ~> (Or T R);
        OrCongR . | S ~> T |- (Or L S) ~> (Or L T);
        XorCongL . | S ~> T |- (Xor S R) ~> (Xor T R);
        XorCongR . | S ~> T |- (Xor L S) ~> (Xor L T);
        NotCong . | S ~> T |- (Not S) ~> (Not T);
        // String operations
        LenCong . | S ~> T |- (Len S) ~> (Len T);
        ConcatCongL . | S ~> T |- (Concat S R) ~> (Concat T R);
        ConcatCongR . | S ~> T |- (Concat L S) ~> (Concat L T);
        AddStrCongL . | S ~> T |- (AddStr S R) ~> (AddStr T R);
        AddStrCongR . | S ~> T |- (AddStr L S) ~> (AddStr L T);
        // Int operations
        AddIntCongL . | S ~> T |- (AddInt S R) ~> (AddInt T R);
        AddIntCongR . | S ~> T |- (AddInt L S) ~> (AddInt L T);
        NegCong . | S ~> T |- (Neg S) ~> (Neg T);
        SubIntCongL . | S ~> T |- (SubInt S R) ~> (SubInt T R);
        SubIntCongR . | S ~> T |- (SubInt L S) ~> (SubInt L T);
        MulIntCongL . | S ~> T |- (MulInt S R) ~> (MulInt T R);
        MulIntCongR . | S ~> T |- (MulInt L S) ~> (MulInt L T);
        DivIntCongL . | S ~> T |- (DivInt S R) ~> (DivInt T R);
        DivIntCongR . | S ~> T |- (DivInt L S) ~> (DivInt L T);
        ModIntCongL . | S ~> T |- (ModInt S R) ~> (ModInt T R);
        ModIntCongR . | S ~> T |- (ModInt L S) ~> (ModInt L T);
        PowIntCongL . | S ~> T |- (PowInt S R) ~> (PowInt T R);
        FactCong . | S ~> T |- (Fact S) ~> (Fact T);
        // Float operations
        AddFloatCongL . | S ~> T |- (AddFloat S R) ~> (AddFloat T R);
        AddFloatCongR . | S ~> T |- (AddFloat L S) ~> (AddFloat L T);
        SubFloatCongL . | S ~> T |- (SubFloat S R) ~> (SubFloat T R);
        SubFloatCongR . | S ~> T |- (SubFloat L S) ~> (SubFloat L T);
        MulFloatCongL . | S ~> T |- (MulFloat S R) ~> (MulFloat T R);
        MulFloatCongR . | S ~> T |- (MulFloat L S) ~> (MulFloat L T);
        DivFloatCongL . | S ~> T |- (DivFloat S R) ~> (DivFloat T R);
        DivFloatCongR . | S ~> T |- (DivFloat L S) ~> (DivFloat L T);
        PowFloatCongL . | S ~> T |- (PowFloat S R) ~> (PowFloat T R);
        PowFloatCongR . | S ~> T |- (PowFloat L S) ~> (PowFloat L T);
        SinFloatCong . | S ~> T |- (SinFloat S) ~> (SinFloat T);
        CosFloatCong . | S ~> T |- (CosFloat S) ~> (CosFloat T);
        ExpFloatCong . | S ~> T |- (ExpFloat S) ~> (ExpFloat T);
        LnFloatCong . | S ~> T |- (LnFloat S) ~> (LnFloat T);
        // Type casts
        IntToFloatCong . | S ~> T |- (IntToFloat S) ~> (IntToFloat T);
        BoolToFloatCong . | S ~> T |- (BoolToFloat S) ~> (BoolToFloat T);
        StrToFloatCong . | S ~> T |- (StrToFloat S) ~> (StrToFloat T);
        FloatToIntCong . | S ~> T |- (FloatToInt S) ~> (FloatToInt T);
        BoolToIntCong . | S ~> T |- (BoolToInt S) ~> (BoolToInt T);
        StrToIntCong . | S ~> T |- (StrToInt S) ~> (StrToInt T);
        BoolToStrCong . | S ~> T |- (BoolToStr S) ~> (BoolToStr T);
        IntToStrCong . | S ~> T |- (IntToStr S) ~> (IntToStr T);
        FloatToStrCong . | S ~> T |- (FloatToStr S) ~> (FloatToStr T);
        IntToBoolCong . | S ~> T |- (IntToBool S) ~> (IntToBool T);
        FloatToBoolCong . | S ~> T |- (FloatToBool S) ~> (FloatToBool T);
        StrToBoolCong . | S ~> T |- (StrToBool S) ~> (StrToBool T);
        IntIdCong . | S ~> T |- (IntId S) ~> (IntId T);
        FloatIdCong . | S ~> T |- (FloatId S) ~> (FloatId T);
        BoolIdCong . | S ~> T |- (BoolId S) ~> (BoolId T);
        StrIdCong . | S ~> T |- (StrId S) ~> (StrId T);
        // Custom operation
        CustomOpCongL . | S ~> T |- (CustomOp S R) ~> (CustomOp T R);
        CustomOpCongR . | S ~> T |- (CustomOp L S) ~> (CustomOp L T);
        // Ternary conditional
        TernCongC . | S ~> T |- (Tern S R1 R2) ~> (Tern T R1 R2);
        TernCongT . | S ~> T |- (Tern L S R) ~> (Tern L T R);
        TernCongE . | S ~> T |- (Tern L R S) ~> (Tern L R T);
    },
}
