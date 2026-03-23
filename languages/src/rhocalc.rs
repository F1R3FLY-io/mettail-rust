#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;
use num_traits::{ToPrimitive, Zero};

language! {
    name: RhoCalc,

    types {
        Proc
        Name
        ![i64] as Int
        ![u32] as UInt32
        ![mettail_runtime::CanonicalBigInt] as BigInt
        ![mettail_runtime::CanonicalBigRat] as BigRat
        ![f64] as Float
        ![bool] as Bool
        ![str] as Str
        ![Vec<Proc>] as List ["[", "]", ","]
        ![mettail_runtime::HashBag<Proc>] as Bag [ "#{", "}#", "|" ]
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
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)(i64)?";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::I64)).map_err(|_| ())
            } ]
        }
        BigInt {
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)n";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
            } ]
        }
        BigRat {
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)r";
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
    },

    terms {
        PZero .
        |- "{}" : Proc;

        PDrop . n:Name  |- "*" "(" n ")" : Proc ;

        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;

        POutput . n:Name, q:Proc
        |- n "!" "(" q ")" : Proc ;

        PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
        |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;

        NQuote . p:Proc
        |- "@" "(" p ")" : Name ;

        PNew . ^[xs].p:[Name* -> Proc]
        |- "new" "(" xs.*sep(",") ")" "in" "{" p "}" : Proc;

        // customize error handling
        // (e.g. filter results by =/= Err)
        Err . |- "error" : Proc;

        // cast rust-native types as processes
        // Order matters for literals: more specific integer kinds (u32, BigInt) before i64 Int
        // so tokens like `1n` / `1u32` are not rejected by the Int prefix arm.
        CastBigRat . r:BigRat |- r : Proc;
        CastFloat . k:Float |- k : Proc;
        CastBigInt . n:BigInt |- n : Proc;
        CastUInt32 . u:UInt32 |- u : Proc;
        CastInt . k:Int |- k : Proc;
        CastBool . k:Bool |- k : Proc;
        CastStr . s:Str |- s : Proc;
        CastList . l:List |- l : Proc;
        CastBag . b:Bag |- b : Proc;
        CastMap . m:Map |- m : Proc;

        FractionProc . a:Proc, b:Proc |- "fraction" "(" a "," b ")" : Proc ![
            { match (&a, &b) {
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(na), BigInt::NumLit(nb)) => {
                        match mettail_runtime::CanonicalBigRat::try_from_nd(na.get().clone(), nb.get().clone()) {
                            Some(r) => Proc::CastBigRat(Box::new(BigRat::RatLit(r))),
                            None => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] step;

        // Infix precedence (declaration order = loosest → tightest for PraTTaIL):
        // or/and, then comparisons, then arithmetic — so `a/b == c/d` and `x==y and z==w` parse correctly.
        Or . a:Proc, b:Proc |- a "or" b : Proc ![
            { match (&a, &b) {
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(*x || *y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        And . a:Proc, b:Proc |- a "and" b : Proc ![
            { match (&a, &b) {
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(*x && *y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Eq . a:Proc, b:Proc |- a "==" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x == y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Ne . a:Proc, b:Proc |- a "!=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x != y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Gt . a:Proc, b:Proc |- a ">" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x > y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Lt . a:Proc, b:Proc |- a "<" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x < y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        GtEq . a:Proc, b:Proc |- a ">=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x >= y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        LtEq . a:Proc, b:Proc |- a "<=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(i), UInt32::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(i), BigInt::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(i), BigRat::RatLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x <= y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        // Arithmetic (tighter than == and and/or)
        Add . a:Proc, b:Proc |- a "+" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(Box::new(*a.clone() + *b.clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => Proc::CastUInt32(Box::new(UInt32::NumLit(x + y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => Proc::CastBigInt(Box::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() + y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => Proc::CastBigRat(Box::new(BigRat::RatLit(*x + *y))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(Box::new(*a.clone() + *b.clone())),
                (Proc::CastStr(a), Proc::CastStr(b)) => match (&**a, &**b) {
                    (Str::StringLit(x), Str::StringLit(y)) => Proc::CastStr(Box::new(Str::StringLit(format!("{}{}", x, y)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Sub . a:Proc, b:Proc |- a "-" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(Box::new(*a.clone() - *b.clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => Proc::CastUInt32(Box::new(UInt32::NumLit(x - y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => Proc::CastBigInt(Box::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() - y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => Proc::CastBigRat(Box::new(BigRat::RatLit(*x - *y))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(Box::new(*a.clone() - *b.clone())),
                _ => Proc::Err,
            }}
        ] fold;

        Mul . a:Proc, b:Proc |- a "*" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(Box::new(*a.clone() * *b.clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => Proc::CastUInt32(Box::new(UInt32::NumLit(x * y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => Proc::CastBigInt(Box::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() * y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => Proc::CastBigRat(Box::new(BigRat::RatLit(*x * *y))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(Box::new(*a.clone() * *b.clone())),
                _ => Proc::Err,
            }}
        ] fold;

        Div . a:Proc, b:Proc |- a "/" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(Box::new(*a.clone() / *b.clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => {
                        if *y == 0 { Proc::Err } else { Proc::CastUInt32(Box::new(UInt32::NumLit(x / y))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => {
                        if y.get().is_zero() { Proc::Err } else { Proc::CastBigInt(Box::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() / y.get())))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => {
                        if y.get().is_zero() { Proc::Err } else { Proc::CastBigRat(Box::new(BigRat::RatLit(*x / *y))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(Box::new(*a.clone() / *b.clone())),
                _ => Proc::Err,
            }}
        ] fold;

        // List operations: take Proc, match CastList/ListLit in semantic (like arithmetic)
        ConcatList . a:Proc, b:Proc |- "concat" "(" a "," b ")" : Proc ![
            { match (&a, &b) {
                (Proc::CastList(la), Proc::CastList(lb)) => match (la.as_ref(), lb.as_ref()) {
                    (List::ListLit(va), List::ListLit(vb)) => { let mut o = va.clone(); o.extend(vb.iter().cloned()); Proc::CastList(Box::new(List::ListLit(o))) },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        ElemList . a:Proc, i:Proc |- "at" "(" a "," i ")" : Proc ![
            { match (&a, &i) {
                (Proc::CastList(l), Proc::CastInt(ii)) => match (l.as_ref(), &**ii) { (List::ListLit(v), Int::NumLit(n)) => v.get(*n as usize).cloned().expect("at: index out of bounds"), _ => Proc::Err },
                _ => Proc::Err,
            }}
        ] fold;
        DeleteList . a:Proc, i:Proc |- "delete" "(" a "," i ")" : Proc ![
            { match (&a, &i) {
                (Proc::CastList(l), Proc::CastInt(ii)) => match (l.as_ref(), &**ii) {
                    (List::ListLit(v), Int::NumLit(n)) => { let idx = *n as usize; let mut vec = v.clone(); if idx >= vec.len() { panic!("delete: index out of bounds"); } vec.remove(idx); Proc::CastList(Box::new(List::ListLit(vec))) },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        // Bag operations: take Proc, match CastBag/BagLit in semantic (like arithmetic)
        UnionBag . a:Proc, b:Proc |- "union" "(" a "," b ")" : Proc ![
            { match (&a, &b) {
                (Proc::CastBag(ba), Proc::CastBag(bb)) => match (ba.as_ref(), bb.as_ref()) {
                    (Bag::BagLit(ha), Bag::BagLit(hb)) => Proc::CastBag(Box::new(Bag::BagLit(ha.union(hb)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        RemoveBag . a:Proc, e:Proc |- "remove" "(" a "," e ")" : Proc ![
            { match &a {
                Proc::CastBag(b) => match b.as_ref() { Bag::BagLit(h) => Proc::CastBag(Box::new(Bag::BagLit(h.remove_one(&e)))), _ => Proc::Err },
                _ => Proc::Err,
            }}
        ] fold;
        DiffBag . a:Proc, b:Proc |- "diff" "(" a "," b ")" : Proc ![
            { match (&a, &b) {
                (Proc::CastBag(ba), Proc::CastBag(bb)) => match (ba.as_ref(), bb.as_ref()) {
                    (Bag::BagLit(ha), Bag::BagLit(hb)) => Proc::CastBag(Box::new(Bag::BagLit(ha.diff(hb)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        CountBag . b:Proc, e:Proc |- "count" "(" b "," e ")" : Int ![
            { match &b {
                Proc::CastBag(bag) => match bag.as_ref() { Bag::BagLit(h) => mettail_runtime::HashBag::count(h, &e) as i64, _ => panic!("count: expected bag literal") }, _ => panic!("count: expected CastBag")
            }}
        ] fold;

        // Map operations: take Proc (CastMap/MapLit), return Proc
        GetMap . m:Proc, k:Proc |- "get" "(" m "," k ")" : Proc ![
            { match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => payload.get(&k).cloned().unwrap_or(Proc::Err),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        PutMap . m:Proc, k:Proc, v:Proc |- "put" "(" m "," k "," v ")" : Proc ![
            { match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => {
                        let mut new_map = payload.clone();
                        new_map.insert(k.clone(), v.clone());
                        Proc::CastMap(Box::new(Map::MapLit(new_map)))
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        DeleteMap . m:Proc, k:Proc |- "mapdelete" "(" m "," k ")" : Proc ![
            { match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => {
                        let mut new_map = payload.clone();
                        new_map.remove(&k);
                        Proc::CastMap(Box::new(Map::MapLit(new_map)))
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        MergeMap . a:Proc, b:Proc |- "merge" "(" a "," b ")" : Proc ![
            { match (&a, &b) {
                (Proc::CastMap(ma), Proc::CastMap(mb)) => match (ma.as_ref(), mb.as_ref()) {
                    (Map::MapLit(pa), Map::MapLit(pb)) => {
                        let mut m = pa.clone();
                        for (k, v) in pb.iter() { m.insert(k.clone(), v.clone()); }
                        Proc::CastMap(Box::new(Map::MapLit(m)))
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        HasMap . m:Proc, k:Proc |- "has" "(" m "," k ")" : Proc ![
            { match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => Proc::CastBool(Box::new(Bool::BoolLit(payload.get(&k).is_some()))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        KeysMap . m:Proc |- "keys" "(" m ")" : Proc ![
            { match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => Proc::CastList(Box::new(List::ListLit(payload.iter().map(|(k, _)| k.clone()).collect::<Vec<_>>()))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        ValuesMap . m:Proc |- "values" "(" m ")" : Proc ![
            { match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => Proc::CastList(Box::new(List::ListLit(payload.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>()))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Not . a:Proc |- "not" a : Proc ![
            { match &a {
                Proc::CastBool(b) => match &**b {
                    Bool::BoolLit(v) => Proc::CastBool(Box::new(Bool::BoolLit(!v))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Len . p:Proc |- "len" "(" p ")" : Proc ![
            { match &p {
                Proc::CastStr(inner) => match &**inner {
                    Str::StringLit(x) => Proc::CastInt(Box::new(Int::NumLit(x.len() as i64))),
                    _ => Proc::Err,
                },
                Proc::CastList(l) => match l.as_ref() {
                    List::ListLit(v) => Proc::CastInt(Box::new(Int::NumLit(v.len() as i64))),
                    _ => Proc::Err,
                },
                Proc::CastMap(m) => match m.as_ref() {
                    Map::MapLit(ref payload) => Proc::CastInt(Box::new(Int::NumLit(payload.len() as i64))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        ToInt . p:Proc |- "int" "(" p ")" : Proc ![
            { match &p {
                Proc::CastInt(x) => Proc::CastInt(x.clone()),
                Proc::CastUInt32(x) => match &**x {
                    UInt32::NumLit(u) => Proc::CastInt(Box::new(Int::NumLit(*u as i64))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match &**x {
                    BigInt::NumLit(n) => match ToPrimitive::to_i64(n.get()) {
                        Some(v) => Proc::CastInt(Box::new(Int::NumLit(v))),
                        None => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match &**x {
                    BigRat::RatLit(r) => match ToPrimitive::to_f64(r.get()) {
                        Some(f) => Proc::CastInt(Box::new(Int::NumLit(f as i64))),
                        None => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                Proc::CastFloat(x) => match &**x {
                    Float::FloatLit(f) => Proc::CastInt(Box::new(Int::NumLit(f.get() as i64))),
                    _ => Proc::Err,
                },
                Proc::CastBool(x) => match &**x {
                    Bool::BoolLit(b) => Proc::CastInt(Box::new(Int::NumLit(if *b { 1 } else { 0 }))),
                    _ => Proc::Err,
                },
                Proc::CastStr(x) => match &**x {
                    Str::StringLit(s) => Proc::CastInt(Box::new(Int::NumLit(s.parse().unwrap_or(0)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        ToFloat . p:Proc |- "float" "(" p ")" : Proc ![
            { match &p {
                Proc::CastFloat(x) => Proc::CastFloat(x.clone()),
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(i) => Proc::CastFloat(Box::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(*i as f64)))),
                    _ => Proc::Err,
                },
                Proc::CastUInt32(x) => match &**x {
                    UInt32::NumLit(u) => Proc::CastFloat(Box::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(*u as f64)))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match &**x {
                    BigInt::NumLit(n) => match ToPrimitive::to_f64(n.get()) {
                        Some(f) => Proc::CastFloat(Box::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(f)))),
                        None => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match &**x {
                    BigRat::RatLit(r) => match ToPrimitive::to_f64(r.get()) {
                        Some(f) => Proc::CastFloat(Box::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(f)))),
                        None => Proc::Err,
                    },
                    _ => Proc::Err,
                },
                Proc::CastBool(x) => match &**x {
                    Bool::BoolLit(b) => Proc::CastFloat(Box::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(if *b { 1.0 } else { 0.0 })))),
                    _ => Proc::Err,
                },
                Proc::CastStr(x) => match &**x {
                    Str::StringLit(s) => Proc::CastFloat(Box::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(s.parse::<f64>().unwrap_or(0.0))))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        ToBool . p:Proc |- "bool" "(" p ")" : Proc ![
            { match &p {
                Proc::CastBool(x) => Proc::CastBool(x.clone()),
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(i) => Proc::CastBool(Box::new(Bool::BoolLit(*i != 0))),
                    _ => Proc::Err,
                },
                Proc::CastUInt32(x) => match &**x {
                    UInt32::NumLit(u) => Proc::CastBool(Box::new(Bool::BoolLit(*u != 0))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match &**x {
                    BigInt::NumLit(n) => Proc::CastBool(Box::new(Bool::BoolLit(!n.get().is_zero()))),
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match &**x {
                    BigRat::RatLit(r) => Proc::CastBool(Box::new(Bool::BoolLit(!r.get().is_zero()))),
                    _ => Proc::Err,
                },
                Proc::CastFloat(x) => match &**x {
                    Float::FloatLit(f) => Proc::CastBool(Box::new(Bool::BoolLit(f.get() != 0.0))),
                    _ => Proc::Err,
                },
                Proc::CastStr(x) => match &**x {
                    Str::StringLit(s) => Proc::CastBool(Box::new(Bool::BoolLit(s.parse::<bool>().unwrap_or(false)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        ToStr . p:Proc |- "str" "(" p ")" : Proc ![
            { match &p {
                Proc::CastStr(x) => Proc::CastStr(x.clone()),
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(i) => Proc::CastStr(Box::new(Str::StringLit(i.to_string()))),
                    _ => Proc::Err,
                },
                Proc::CastUInt32(x) => match &**x {
                    UInt32::NumLit(u) => Proc::CastStr(Box::new(Str::StringLit(u.to_string()))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match &**x {
                    BigInt::NumLit(n) => Proc::CastStr(Box::new(Str::StringLit(n.to_string()))),
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match &**x {
                    BigRat::RatLit(r) => Proc::CastStr(Box::new(Str::StringLit(r.to_string()))),
                    _ => Proc::Err,
                },
                Proc::CastFloat(x) => match &**x {
                    Float::FloatLit(f) => Proc::CastStr(Box::new(Str::StringLit(f.to_string()))),
                    _ => Proc::Err,
                },
                Proc::CastBool(x) => match &**x {
                    Bool::BoolLit(b) => Proc::CastStr(Box::new(Str::StringLit(b.to_string()))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;


    },

    equations {
        QuoteDrop . |- (NQuote (PDrop N)) = N ;

        Extrude . xs.*map(|x| x # ...rest)
            |- (PPar {(PNew ^[xs].p), ...rest}) = (PNew ^[xs].(PPar {p, ...rest})) ;
    },

    rewrites {

        // communication:
        // (n1 ? x1 , ... , nk ? xk).{ p } | n1!(q1) | ... | nk!(qk) ~> p(@q1,...,@qk)
        Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
            ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});

        Exec . |- (PDrop (NQuote P)) ~> P;

        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});

        NewCong . | S ~> T |- (PNew ^[xs].S) ~> (PNew ^[xs].T);

        // TODO: shorthand to make these in the term declarations
        AddCongL . | S ~> T |- (Add S X) ~> (Add T X);

        AddCongR . | S ~> T |- (Add X S) ~> (Add X T);

        SubCongL . | S ~> T |- (Sub S X) ~> (Sub T X);

        SubCongR . | S ~> T |- (Sub X S) ~> (Sub X T);

        MulCongL . | S ~> T |- (Mul S X) ~> (Mul T X);

        MulCongR . | S ~> T |- (Mul X S) ~> (Mul X T);

        DivCongL . | S ~> T |- (Div S X) ~> (Div T X);

        DivCongR . | S ~> T |- (Div X S) ~> (Div X T);

        EqCongL . | S ~> T |- (Eq S X) ~> (Eq T X);
        EqCongR . | S ~> T |- (Eq X S) ~> (Eq X T);
        NeCongL . | S ~> T |- (Ne S X) ~> (Ne T X);
        NeCongR . | S ~> T |- (Ne X S) ~> (Ne X T);
        GtCongL . | S ~> T |- (Gt S X) ~> (Gt T X);
        GtCongR . | S ~> T |- (Gt X S) ~> (Gt X T);
        LtCongL . | S ~> T |- (Lt S X) ~> (Lt T X);
        LtCongR . | S ~> T |- (Lt X S) ~> (Lt X T);
        GtEqCongL . | S ~> T |- (GtEq S X) ~> (GtEq T X);
        GtEqCongR . | S ~> T |- (GtEq X S) ~> (GtEq X T);
        LtEqCongL . | S ~> T |- (LtEq S X) ~> (LtEq T X);
        LtEqCongR . | S ~> T |- (LtEq X S) ~> (LtEq X T);

        NotCong . | S ~> T |- (Not S) ~> (Not T);
        AndCongL . | S ~> T |- (And S X) ~> (And T X);
        AndCongR . | S ~> T |- (And X S) ~> (And X T);
        OrCongL . | S ~> T |- (Or S X) ~> (Or T X);
        OrCongR . | S ~> T |- (Or X S) ~> (Or X T);

        LenCong . | S ~> T |- (Len S) ~> (Len T);

        ConcatListCongL . | S ~> T |- (ConcatList S X) ~> (ConcatList T X);
        ConcatListCongR . | S ~> T |- (ConcatList X S) ~> (ConcatList X T);
        ElemListCongL . | S ~> T |- (ElemList S X) ~> (ElemList T X);
        ElemListCongR . | S ~> T |- (ElemList X S) ~> (ElemList X T);
        DeleteListCongL . | S ~> T |- (DeleteList S X) ~> (DeleteList T X);
        DeleteListCongR . | S ~> T |- (DeleteList X S) ~> (DeleteList X T);
        UnionBagCongL . | S ~> T |- (UnionBag S X) ~> (UnionBag T X);
        UnionBagCongR . | S ~> T |- (UnionBag X S) ~> (UnionBag X T);
        RemoveBagCongL . | S ~> T |- (RemoveBag S X) ~> (RemoveBag T X);
        RemoveBagCongR . | S ~> T |- (RemoveBag X S) ~> (RemoveBag X T);
        DiffBagCongL . | S ~> T |- (DiffBag S X) ~> (DiffBag T X);
        DiffBagCongR . | S ~> T |- (DiffBag X S) ~> (DiffBag X T);
        CountBagCongL . | S ~> T |- (CountBag S X) ~> (CountBag T X);
        CountBagCongR . | S ~> T |- (CountBag X S) ~> (CountBag X T);

        GetMapCongL . | S ~> T |- (GetMap S X) ~> (GetMap T X);
        GetMapCongR . | S ~> T |- (GetMap X S) ~> (GetMap X T);
        PutMapCongL . | S ~> T |- (PutMap S K V) ~> (PutMap T K V);
        PutMapCongKey . | S ~> T |- (PutMap M S V) ~> (PutMap M T V);
        PutMapCongVal . | S ~> T |- (PutMap M K S) ~> (PutMap M K T);
        DeleteMapCongL . | S ~> T |- (DeleteMap S X) ~> (DeleteMap T X);
        DeleteMapCongR . | S ~> T |- (DeleteMap X S) ~> (DeleteMap X T);
        MergeMapCongL . | S ~> T |- (MergeMap S X) ~> (MergeMap T X);
        MergeMapCongR . | S ~> T |- (MergeMap X S) ~> (MergeMap X T);
        HasMapCongL . | S ~> T |- (HasMap S X) ~> (HasMap T X);
        HasMapCongR . | S ~> T |- (HasMap X S) ~> (HasMap X T);
        KeysMapCong . | S ~> T |- (KeysMap S) ~> (KeysMap T);
        ValuesMapCong . | S ~> T |- (ValuesMap S) ~> (ValuesMap T);

        CastMapCong . | S ~> T |- (CastMap S) ~> (CastMap T);
        CastIntCong . | S ~> T |- (CastInt S) ~> (CastInt T);
        CastUInt32Cong . | S ~> T |- (CastUInt32 S) ~> (CastUInt32 T);
        CastBigIntCong . | S ~> T |- (CastBigInt S) ~> (CastBigInt T);
        CastBigRatCong . | S ~> T |- (CastBigRat S) ~> (CastBigRat T);
        FractionProcCongL . | S ~> T |- (FractionProc S X) ~> (FractionProc T X);
        FractionProcCongR . | S ~> T |- (FractionProc X S) ~> (FractionProc X T);
        ToIntCong . | S ~> T |- (ToInt S) ~> (ToInt T);
        ToFloatCong . | S ~> T |- (ToFloat S) ~> (ToFloat T);
        ToBoolCong . | S ~> T |- (ToBool S) ~> (ToBool T);
        ToStrCong . | S ~> T |- (ToStr S) ~> (ToStr T);
    },

    logic {
        // fold *(@(P)) to P so that remove(*(@(bag)), *(@(elem))) can reduce (Exec semantics in fold)
        fold_proc(s.clone(), res) <--
            proc(s),
            if let Proc::PDrop(ref n) = s,
            if let Name::NQuote(ref p) = n.as_ref(),
            let res = p.as_ref().clone();

        // many-step to a result
        relation path(Proc, Proc);
        path(p0, p1) <-- rw_proc(p0, p1);
        path(p0, p2) <-- path(p0, p1), path(p1, p2);

        // or we can store every step!
        relation path_vec(Vec<Proc>);
        path_vec(xs) <--
            proc(x0), rw_proc(x0,x1),
            let xs = vec![x0.clone(), x1.clone()];
        path_vec(zs) <--
            path_vec(xs), path_vec(ys),
            if xs.last() == ys.first(),
            let zs = [xs.as_slice(), ys.as_slice()].concat();

        // paths where term size (display length) strictly decreases at every step
        // TODO: currently makes execution slow; investigate why
        // relation shrinking_path(Vec<Proc>);
        // shrinking_path(xs) <--
        //     path_vec(xs),
        //     if xs.windows(2).all(|w| w[0].to_string().len() > w[1].to_string().len());

        // context-labelled transition system:
        // p -c-> q if c(p)~>q
        relation trans(Proc, Proc, Proc);
        trans(p,c,q) <--
            step_term(p), proc(c),
            if let Proc::LamProc(_) = c,
            let app = Proc::ApplyProc(Box::new(c.clone()), Box::new(p.clone())),
            let res = app.normalize(),
            path(res.clone(), q);

        trans(p,c,q) <--
            step_term(p), proc(c),
            if let Proc::MLamProc(_) = c,
            let app = Proc::MApplyProc(Box::new(c.clone()), vec![p.clone()]),
            let res = app.normalize(),
            path(res.clone(), q);

        // contexts for testing (TODO: auto-generate)
        // proc(p) <-- if let Ok(p) = Proc::parse("^x.{{ x | serv!(req) }}");
        // proc(p) <-- if let Ok(p) = Proc::parse("^x.{x}");

        // rules to add c(p) to the set of processes
        proc(res) <--
            step_term(p), proc(c),
            if let Proc::LamProc(_) = c,
            let app = Proc::ApplyProc(Box::new(c.clone()), Box::new(p.clone())),
            let res = app.normalize();
        proc(res) <--
            step_term(p), proc(c),
            if let Proc::MLamProc(_) = c,
            let app = Proc::MApplyProc(Box::new(c.clone()), vec![p.clone()]),
            let res = app.normalize();

        // relation garbage(Name,Proc);
        // garbage(n,p) <--
        //     proc(p),name(n),
        //     !(proc(k), trans(p,k,q), can_comm(q,n));
    },
}
