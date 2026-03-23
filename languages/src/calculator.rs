#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Calculator,
    types {
        Proc
        ![i32] as Int
        ![u32] as UInt32
        ![mettail_runtime::CanonicalBigInt] as BigInt
        ![mettail_runtime::CanonicalBigRat] as BigRat
        ![f64] as Float
        ![bool] as Bool
        ![str] as Str
        ![Vec<Proc>] as List
        ![mettail_runtime::HashBag<Proc>] as Bag
        ![HashMap<Proc, Proc>] as Map
    },
    literals {
        UInt32 {
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)u32";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
            } ]
        }
        Int {
            // Int (i32) literals; unsuffixed defaults to i32.
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)(i32)?";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::I32)).map_err(|_| ())
            } ]
        }
        BigInt {
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)n";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
            } ]
        }
        // BigRat sugar: `<int>r` (whole) or `<int>r/<int>r` (composite); radix/`_` parity with BigInt `n` literals.
        BigRat {
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)r(/(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)r)?";
            eval: ![ {
                mettail_prattail::parse_rational_lit(text).map_err(|_| ())
            } ]
        }
        Float {
            // Require decimal point or exponent so e.g. "3" is not matched (stays integer).
            pattern: r"[0-9](_?[0-9])*(\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?|[eE][+-]?[0-9](_?[0-9])*)|\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?";
            eval: ![ {
                // Strip digit separators (e.g. 1_000_000.5) before parsing.
                let cleaned = text.replace('_', "");
                cleaned.parse::<f64>()
            } ]
        }
        Bool {
            pattern: r"yeap|nope|true|false";
            eval: ![ {
                match text {
                    "yeap" => Ok(true),
                    "nope" => Ok(false),
                    "true" => Ok(true),
                    "false" => Ok(false),
                    _ => Err(()),
                }
            } ]
        }
        Str {
            pattern: r#""([^"\\]|\\.)*""#;
            eval: ![ {
                if text.len() < 2 {
                    Err(())
                } else {
                    let inner = &text[1..text.len()-1];
                    let unescaped = inner
                        .replace("\\\"", "\"")
                        .replace("\\\\", "\\");
                    Ok(unescaped.to_string())
                }
            } ]
        }
    },
    terms {
        // Injection into Proc (unified variant) so List/Bag elements are Proc
        ProcInt . i:Int |- i : Proc ;
        ProcFloat . f:Float |- f : Proc ;
        ProcBool . b:Bool |- b : Proc ;
        ProcStr . s:Str |- s : Proc ;
        ProcList . l:List |- l : Proc ;
        ProcBag . b:Bag |- b : Proc ;
        ProcMap . m:Map |- m : Proc ;
        ProcUInt32 . u:UInt32 |- u : Proc ;
        ProcBigInt . n:BigInt |- n : Proc ;
        ProcBigRat . r:BigRat |- r : Proc ;
        Fraction . a:BigInt, b:BigInt |- "fraction" "(" a "," b ")" : BigRat ![{
            mettail_runtime::CanonicalBigRat::try_from_nd(a.get().clone(), b.get().clone())
                .expect("fraction: zero denominator")
        }] step;
        AddBigRat . a:BigRat, b:BigRat |- a "+" b : BigRat ![a + b] fold;
        MulBigRat . a:BigRat, b:BigRat |- a "*" b : BigRat ![a * b] fold;
        DivBigRat . a:BigRat, b:BigRat |- a "/" b : BigRat ![a / b] fold;
        NegBigRat . a:BigRat |- "-" a : BigRat ![(-a)] fold;
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
        //
        AddUInt32 . a:UInt32, b:UInt32 |- a "+" b : UInt32 ![a + b] fold;
        AddBigInt . a:BigInt, b:BigInt |- a "+" b : BigInt ![a + b] fold;
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
        // Proc → concrete type projections (runtime type extraction)
        // These are fold rules: fold_proc reduces ElemList → injection variant before rust_code runs
        ProcToInt . a:Proc |- "int" "(" a ")" : Int ![{
            match a {
                Proc::ProcInt(i) => i.as_ref().eval(),
                Proc::ProcFloat(f) => f.as_ref().eval().get() as i32,
                Proc::ProcBool(b) => if b.as_ref().eval() { 1 } else { 0 },
                Proc::ProcStr(s) => s.as_ref().eval().parse().unwrap_or(0),
                Proc::ElemList(list, index) => {
                    let idx = match index.as_ref() { Int::NumLit(n) => *n as usize, _ => panic!("ElemList: expected Int literal") };
                    let elem = match list.as_ref() { List::ListLit(v) => v.get(idx).cloned().expect("ElemList: index out of bounds"), _ => panic!("int(): ElemList list not a literal") };
                    match elem {
                        Proc::ProcInt(i) => i.as_ref().eval(),
                        Proc::ProcFloat(f) => f.as_ref().eval().get() as i32,
                        Proc::ProcBool(b) => if b.as_ref().eval() { 1 } else { 0 },
                        Proc::ProcStr(s) => s.as_ref().eval().parse().unwrap_or(0),
                        other => panic!("int(): cannot convert list element to Int: {:?}", other),
                    }
                }
                other => panic!("int(): cannot convert Proc variant to Int: {:?}", other),
            }
        }] fold;
        ProcToFloat . a:Proc |- "float" "(" a ")" : Float ![{
            match a {
                Proc::ProcFloat(f) => f.as_ref().eval(),
                Proc::ProcInt(i) => mettail_runtime::CanonicalFloat64::from(i.as_ref().eval() as f64),
                Proc::ProcBool(b) => mettail_runtime::CanonicalFloat64::from(if b.as_ref().eval() { 1.0 } else { 0.0 }),
                Proc::ProcStr(s) => mettail_runtime::CanonicalFloat64::from(s.as_ref().eval().parse::<f64>().unwrap_or(0.0)),
                Proc::ElemList(list, index) => {
                    let idx = match index.as_ref() { Int::NumLit(n) => *n as usize, _ => panic!("ElemList: expected Int literal") };
                    let elem = match list.as_ref() { List::ListLit(v) => v.get(idx).cloned().expect("ElemList: index out of bounds"), _ => panic!("float(): ElemList list not a literal") };
                    match elem {
                        Proc::ProcFloat(f) => f.as_ref().eval(),
                        Proc::ProcInt(i) => mettail_runtime::CanonicalFloat64::from(i.as_ref().eval() as f64),
                        Proc::ProcBool(b) => mettail_runtime::CanonicalFloat64::from(if b.as_ref().eval() { 1.0 } else { 0.0 }),
                        Proc::ProcStr(s) => mettail_runtime::CanonicalFloat64::from(s.as_ref().eval().parse::<f64>().unwrap_or(0.0)),
                        other => panic!("float(): cannot convert list element to Float: {:?}", other),
                    }
                }
                other => panic!("float(): cannot convert Proc variant to Float: {:?}", other),
            }
        }] fold;
        ProcToBool . a:Proc |- "bool" "(" a ")" : Bool ![{
            match a {
                Proc::ProcBool(b) => b.as_ref().eval(),
                Proc::ProcInt(i) => i.as_ref().eval() != 0,
                Proc::ProcFloat(f) => f.as_ref().eval().get() != 0.0,
                Proc::ProcStr(s) => s.as_ref().eval().parse().unwrap_or(false),
                Proc::ElemList(list, index) => {
                    let idx = match index.as_ref() { Int::NumLit(n) => *n as usize, _ => panic!("ElemList: expected Int literal") };
                    let elem = match list.as_ref() { List::ListLit(v) => v.get(idx).cloned().expect("ElemList: index out of bounds"), _ => panic!("bool(): ElemList list not a literal") };
                    match elem {
                        Proc::ProcBool(b) => b.as_ref().eval(),
                        Proc::ProcInt(i) => i.as_ref().eval() != 0,
                        Proc::ProcFloat(f) => f.as_ref().eval().get() != 0.0,
                        Proc::ProcStr(s) => s.as_ref().eval().parse().unwrap_or(false),
                        other => panic!("bool(): cannot convert list element to Bool: {:?}", other),
                    }
                }
                other => panic!("bool(): cannot convert Proc variant to Bool: {:?}", other),
            }
        }] fold;
        ProcToStr . a:Proc |- "str" "(" a ")" : Str ![{
            match a {
                Proc::ProcStr(s) => s.as_ref().eval(),
                Proc::ProcInt(i) => i.as_ref().eval().to_string(),
                Proc::ProcFloat(f) => f.as_ref().eval().to_string(),
                Proc::ProcBool(b) => b.as_ref().eval().to_string(),
                Proc::ElemList(list, index) => {
                    let idx = match index.as_ref() { Int::NumLit(n) => *n as usize, _ => panic!("ElemList: expected Int literal") };
                    let elem = match list.as_ref() { List::ListLit(v) => v.get(idx).cloned().expect("ElemList: index out of bounds"), _ => panic!("str(): ElemList list not a literal") };
                    match elem {
                        Proc::ProcStr(s) => s.as_ref().eval(),
                        Proc::ProcInt(i) => i.as_ref().eval().to_string(),
                        Proc::ProcFloat(f) => f.as_ref().eval().to_string(),
                        Proc::ProcBool(b) => b.as_ref().eval().to_string(),
                        other => panic!("str(): cannot convert list element to Str: {:?}", other),
                    }
                }
                other => panic!("str(): cannot convert Proc variant to Str: {:?}", other),
            }
        }] fold;
        // Custom operation (PraTTaIL test feature)
        CustomOp . a:Int, b:Int |- a "~" b : Int ![2 * a + 3 * b] fold;
        // List operations (List = Vec<Proc>). Fold/step pass payloads; rust_code returns payload.
        ConcatList . a:List, b:List |- "concat" "(" a "," b ")" : List ![
            { let mut o = a.clone(); o.extend(b.iter().cloned()); o }
        ] fold;
        LenList . a:List |- "length" "(" a ")" : Int ![
            a.len() as i32
        ] fold;
        ElemList . a:List, i:Int |- "at" "(" a "," i ")" : Proc ![
            { let idx = match &i { Int::NumLit(n) => *n as usize, _ => panic!("ElemList: expected Int literal") }; a.get(idx).cloned().expect("ElemList: index out of bounds") }
        ] fold;
        DeleteList . a:List, i:Int |- "delete" "(" a "," i ")" : List ![
            { let idx = match &i { Int::NumLit(n) => *n as usize, _ => panic!("DeleteList: expected Int literal") }; let mut v = a.clone(); if idx >= v.len() { panic!("DeleteList: index out of bounds"); } v.remove(idx); v }
        ] fold;
        // Bag operations (Bag = HashBag<Proc>). Fold passes payloads; rust_code returns payload.
        UnionBag . a:Bag, b:Bag |- "union" "(" a "," b ")" : Bag ![a.union(&b)] fold;
        RemoveBag . a:Bag, e:Proc |- "remove" "(" a "," e ")" : Bag ![a.remove_one(&e)] fold;
        DiffBag . a:Bag, b:Bag |- "diff" "(" a "," b ")" : Bag ![a.diff(&b)] fold;
        CountBag . b:Bag, e:Proc |- "count" "(" b "," e ")" : Int ![{ mettail_runtime::HashBag::count(&b, &e) as i32 }] fold;
        // Map operations (Map = HashMapLit<Proc, Proc>). Use "maplength" to avoid ambiguous dispatch with length(List).
        LenMap . a:Map |- "maplength" "(" a ")" : Int ![
            a.len() as i32
        ] fold;
        GetMap . m:Map, k:Proc |- "get" "(" m "," k ")" : Proc ![
            m.get(&k).cloned().expect("get: key not found")
        ] fold;
        PutMap . m:Map, k:Proc, v:Proc |- "put" "(" m "," k "," v ")" : Map ![
            { let mut m = m.clone(); m.insert(k.clone(), v.clone()); m }
        ] fold;
        DeleteMap . m:Map, k:Proc |- "delete" "(" m "," k ")" : Map ![
            { let mut m = m.clone(); m.remove(&k); m }
        ] fold;
        MergeMap . a:Map, b:Map |- "merge" "(" a "," b ")" : Map ![
            { let mut m = a.clone(); for (k, v) in b.iter() { m.insert(k.clone(), v.clone()); } m }
        ] fold;
        HasMap . m:Map, k:Proc |- "has" "(" m "," k ")" : Bool ![
            m.get(&k).is_some()
        ] fold;
        KeysMap . m:Map |- "keys" "(" m ")" : List ![
            m.iter().map(|(k, _)| k.clone()).collect::<Vec<_>>()
        ] fold;
        ValuesMap . m:Map |- "values" "(" m ")" : List ![
            m.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>()
        ] fold;
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
        // Proc → concrete type projection congruence
        ProcToIntCong . | S ~> T |- (ProcToInt S) ~> (ProcToInt T);
        ProcToFloatCong . | S ~> T |- (ProcToFloat S) ~> (ProcToFloat T);
        ProcToBoolCong . | S ~> T |- (ProcToBool S) ~> (ProcToBool T);
        ProcToStrCong . | S ~> T |- (ProcToStr S) ~> (ProcToStr T);
        // Proc (unified variant) congruence
        ProcIntCong . | S ~> T |- (ProcInt S) ~> (ProcInt T);
        ProcFloatCong . | S ~> T |- (ProcFloat S) ~> (ProcFloat T);
        ProcBoolCong . | S ~> T |- (ProcBool S) ~> (ProcBool T);
        ProcStrCong . | S ~> T |- (ProcStr S) ~> (ProcStr T);
        ProcListCong . | S ~> T |- (ProcList S) ~> (ProcList T);
        ProcBagCong . | S ~> T |- (ProcBag S) ~> (ProcBag T);
        ProcMapCong . | S ~> T |- (ProcMap S) ~> (ProcMap T);
        // Map operations
        LenMapCong . | S ~> T |- (LenMap S) ~> (LenMap T);
        GetMapCongL . | S ~> T |- (GetMap S R) ~> (GetMap T R);
        GetMapCongR . | S ~> T |- (GetMap L S) ~> (GetMap L T);
        PutMapCongL . | S ~> T |- (PutMap S K V) ~> (PutMap T K V);
        PutMapCongKey . | S ~> T |- (PutMap M S V) ~> (PutMap M T V);
        PutMapCongVal . | S ~> T |- (PutMap M K S) ~> (PutMap M K T);
        DeleteMapCongL . | S ~> T |- (DeleteMap S R) ~> (DeleteMap T R);
        DeleteMapCongR . | S ~> T |- (DeleteMap L S) ~> (DeleteMap L T);
        MergeMapCongL . | S ~> T |- (MergeMap S R) ~> (MergeMap T R);
        MergeMapCongR . | S ~> T |- (MergeMap L S) ~> (MergeMap L T);
        HasMapCongL . | S ~> T |- (HasMap S R) ~> (HasMap T R);
        HasMapCongR . | S ~> T |- (HasMap L S) ~> (HasMap L T);
        KeysMapCong . | S ~> T |- (KeysMap S) ~> (KeysMap T);
        ValuesMapCong . | S ~> T |- (ValuesMap S) ~> (ValuesMap T);
        // Custom operation
        CustomOpCongL . | S ~> T |- (CustomOp S R) ~> (CustomOp T R);
        CustomOpCongR . | S ~> T |- (CustomOp L S) ~> (CustomOp L T);
        // Ternary conditional
        TernCongC . | S ~> T |- (Tern S R1 R2) ~> (Tern T R1 R2);
        TernCongT . | S ~> T |- (Tern L S R) ~> (Tern L T R);
        TernCongE . | S ~> T |- (Tern L R S) ~> (Tern L R T);
        // No List/Bag congruence: only Proc congruence (e.g. ProcList/ProcBag) is needed.
        ProcUInt32Cong . | S ~> T |- (ProcUInt32 S) ~> (ProcUInt32 T);
        AddUInt32CongL . | S ~> T |- (AddUInt32 S R) ~> (AddUInt32 T R);
        AddUInt32CongR . | S ~> T |- (AddUInt32 L S) ~> (AddUInt32 L T);
        ProcBigIntCong . | S ~> T |- (ProcBigInt S) ~> (ProcBigInt T);
        AddBigIntCongL . | S ~> T |- (AddBigInt S R) ~> (AddBigInt T R);
        AddBigIntCongR . | S ~> T |- (AddBigInt L S) ~> (AddBigInt L T);
        ProcBigRatCong . | S ~> T |- (ProcBigRat S) ~> (ProcBigRat T);
        FractionCongN . | S ~> T |- (Fraction S R) ~> (Fraction T R);
        FractionCongD . | S ~> T |- (Fraction L S) ~> (Fraction L T);
        AddBigRatCongL . | S ~> T |- (AddBigRat S R) ~> (AddBigRat T R);
        AddBigRatCongR . | S ~> T |- (AddBigRat L S) ~> (AddBigRat L T);
        MulBigRatCongL . | S ~> T |- (MulBigRat S R) ~> (MulBigRat T R);
        MulBigRatCongR . | S ~> T |- (MulBigRat L S) ~> (MulBigRat L T);
        DivBigRatCongL . | S ~> T |- (DivBigRat S R) ~> (DivBigRat T R);
        DivBigRatCongR . | S ~> T |- (DivBigRat L S) ~> (DivBigRat L T);
        NegBigRatCong . | S ~> T |- (NegBigRat S) ~> (NegBigRat T);
    },
}
