#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;
use num_traits::Zero;
use std::ops::Neg;

language! {
    name: RhoCalc,

    types {
        Proc
        Name
        ![i64] as Int
        ![u32] as UInt32
        ![mettail_runtime::CanonicalBigInt] as BigInt
        ![mettail_runtime::CanonicalBigRat] as BigRat
        ![mettail_runtime::CanonicalFixedPoint] as Fixed
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
            pattern: r"-?(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)n";
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
        Fixed {
            pattern: r"-?([0-9](_?[0-9])*(\.[0-9](_?[0-9])*)?|\.[0-9](_?[0-9])*)p[0-9](_?[0-9])*";
            eval: ![ { mettail_prattail::parse_fixed_lit(text).map_err(|_| ()) } ]
        }
        Float {
            pattern: r"-?([0-9](_?[0-9])*(\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?|[eE][+-]?[0-9](_?[0-9])*)(f64)?|\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?(f64)?)";
            eval: ![ { mettail_prattail::parse_float_lit(text).map_err(|_| ()) } ]
        }
    },

    terms {
        PZero .
        |- "{}" : Proc;

        PDrop . n:Name  |- "*" "(" n ")" : Proc ;

        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;

        POutput . n:Name, q:Proc
        |- n "!" "(" q ")" : Proc ;

        // Pattern-based single-input receive used by guarded COMM.
        PFor . n:Name, pat:Proc, body:Proc
        |- "for" "(" n "<-" pat ")" "." "{" body "}" : Proc;

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
        CastFixed . x:Fixed |- x : Proc;
        CastFloat . k:Float |- k : Proc;
        CastBigInt . n:BigInt |- n : Proc;
        CastUInt32 . u:UInt32 |- u : Proc;
        CastInt . k:Int |- k : Proc;
        CastBool . k:Bool |- k : Proc;
        CastStr . s:Str |- s : Proc;
        CastList . l:List |- l : Proc;
        CastBag . b:Bag |- b : Proc;
        CastMap . m:Map |- m : Proc;

        // Numeric casts (see `docs/design/made/native-types/numeric-casting.md`): binary width required.
        IntBinProc . a:Proc, w:Int |- "int" "(" a "," w ")" : Proc ![{
            crate::numeric_dispatch::rho_proc_int_bin(&a, w)
        }] fold;
        UIntBinProc . a:Proc, w:Int |- "uint" "(" a "," w ")" : Proc ![{
            crate::numeric_dispatch::rho_proc_uint_bin(&a, w)
        }] fold;
        FloatBinProc . a:Proc, w:Int |- "float" "(" a "," w ")" : Proc ![{
            crate::numeric_dispatch::rho_proc_float_bin(&a, w)
        }] fold;
        FixedBinProc . a:Proc, w:Int |- "fixed" "(" a "," w ")" : Proc ![{
            crate::numeric_dispatch::rho_proc_fixed_bin(&a, w)
        }] fold;
        BigintCastProc . a:Proc |- "bigint" "(" a ")" : Proc ![{
            crate::numeric_dispatch::rho_proc_bigint_unary(&a)
        }] fold;
        BigratCastProc . a:Proc |- "bigrat" "(" a ")" : Proc ![{
            crate::numeric_dispatch::rho_proc_bigrat_unary(&a)
        }] fold;

        // Unary minus on Int (width args like `int(x, -7)`) and on Proc (`-7`, `-3r/2r`, …).
        // `NegProc` is declared after `/` and `%` so `-` binds tighter than division (e.g. `-3r/2r` is `(-3r)/2r`).
        NegInt . a:Int |- "-" a : Int ![(-a)] fold;

        // `fold` (not `step`): `step` HOL rules are skipped for non-native categories like Proc.
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
        ] fold;

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

        // Bitwise (looser precedence than arithmetic)
        // Use `bitor` (not `|`) so `{ P | Q }` stays parallel composition (PPar separator).
        BitOr . a:Proc, b:Proc |- a "bitor" b : Proc ![
            { match (&a, &b) {
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(Box::new(Fixed::FixedLit(*x | *y))),
                    _ => Proc::Err,
                },
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => Proc::CastInt(Box::new(Int::NumLit(x | y))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => Proc::CastUInt32(Box::new(UInt32::NumLit(x | y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => Proc::CastBigInt(Box::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() | y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => Proc::CastBigRat(Box::new(BigRat::RatLit(x.bitor_aligned(*y)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        BitAnd . a:Proc, b:Proc |- a "bitand" b : Proc ![
            { match (&a, &b) {
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(Box::new(Fixed::FixedLit(*x & *y))),
                    _ => Proc::Err,
                },
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(x), Int::NumLit(y)) => Proc::CastInt(Box::new(Int::NumLit(x & y))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => Proc::CastUInt32(Box::new(UInt32::NumLit(x & y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => Proc::CastBigInt(Box::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() & y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (&**a, &**b) {
                    (BigRat::RatLit(x), BigRat::RatLit(y)) => Proc::CastBigRat(Box::new(BigRat::RatLit(x.bitand_aligned(*y)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        BitNot . a:Proc |- "bitnot" a : Proc ![
            { match &a {
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(v) => Proc::CastInt(Box::new(Int::NumLit(!v))),
                    _ => Proc::Err,
                },
                Proc::CastUInt32(x) => match &**x {
                    UInt32::NumLit(v) => Proc::CastUInt32(Box::new(UInt32::NumLit(!v))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match &**x {
                    BigInt::NumLit(n) => Proc::CastBigInt(Box::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(!n.get())))),
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match &**x {
                    BigRat::RatLit(r) => Proc::CastBigRat(Box::new(BigRat::RatLit(r.bitnot()))),
                    _ => Proc::Err,
                },
                Proc::CastFixed(x) => match &**x {
                    Fixed::FixedLit(fp) => Proc::CastFixed(Box::new(Fixed::FixedLit(
                        mettail_runtime::CanonicalFixedPoint::new(!fp.unscaled().clone(), fp.places()),
                    ))),
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
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x == y))),
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
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x != y))),
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
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x > y))),
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
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x < y))),
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
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x >= y))),
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
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x <= y))),
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
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(Box::new(Fixed::FixedLit(*x + *y))),
                    _ => Proc::Err,
                },
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
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(Box::new(Fixed::FixedLit(*x - *y))),
                    _ => Proc::Err,
                },
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
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Proc::CastFixed(Box::new(Fixed::FixedLit(*x * *y))),
                    _ => Proc::Err,
                },
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
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => {
                        match x.checked_div(*y) {
                            Some(q) => Proc::CastFixed(Box::new(Fixed::FixedLit(q))),
                            None => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Mod . a:Proc, b:Proc |- a "%" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(Box::new(*a.clone() % *b.clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (&**a, &**b) {
                    (UInt32::NumLit(x), UInt32::NumLit(y)) => {
                        if *y == 0 { Proc::Err } else { Proc::CastUInt32(Box::new(UInt32::NumLit(x % y))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (&**a, &**b) {
                    (BigInt::NumLit(x), BigInt::NumLit(y)) => {
                        if y.get().is_zero() { Proc::Err } else { Proc::CastBigInt(Box::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() % y.get())))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (&**a, &**b) {
                    (Fixed::FixedLit(x), Fixed::FixedLit(y)) => {
                        match x.checked_rem(*y) {
                            Some(r) => Proc::CastFixed(Box::new(Fixed::FixedLit(r))),
                            None => Proc::Err,
                        }
                    }
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        NegProc . a:Proc |- "-" a : Proc ![
            { match &a {
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(n) => Proc::CastInt(Box::new(Int::NumLit(-n))),
                    _ => Proc::Err,
                },
                Proc::CastUInt32(x) => match &**x {
                    UInt32::NumLit(u) => Proc::CastInt(Box::new(Int::NumLit(-(*u as i64)))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match &**x {
                    BigInt::NumLit(n) => Proc::CastBigInt(Box::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(-n.get())))),
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match &**x {
                    BigRat::RatLit(r) => Proc::CastBigRat(Box::new(BigRat::RatLit(r.clone().neg()))),
                    _ => Proc::Err,
                },
                Proc::CastFloat(x) => match &**x {
                    Float::FloatLit(f) => Proc::CastFloat(Box::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(-f.get())))),
                    _ => Proc::Err,
                },
                Proc::CastFixed(x) => match &**x {
                    Fixed::FixedLit(fp) => Proc::CastFixed(Box::new(Fixed::FixedLit(fp.clone().neg()))),
                    _ => Proc::Err,
                },
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
                Proc::CastFixed(x) => match &**x {
                    Fixed::FixedLit(fp) => Proc::CastBool(Box::new(Bool::BoolLit(!Zero::is_zero(fp.unscaled())))),
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
                Proc::CastInt(x) => Proc::CastStr(Box::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastUInt32(x) => Proc::CastStr(Box::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastBigInt(x) => Proc::CastStr(Box::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastBigRat(x) => Proc::CastStr(Box::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastFloat(x) => Proc::CastStr(Box::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastFixed(x) => Proc::CastStr(Box::new(Str::StringLit(x.as_ref().eval().to_string()))),
                Proc::CastBool(x) => Proc::CastStr(Box::new(Str::StringLit(x.as_ref().eval().to_string()))),
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

        // Pattern-based communication (single channel): if payload matches pattern, apply substitution into body.
        CommPattern . | unifies(pat, q) |- (PPar {(PFor n pat body), (POutput n q), ...rest})
            ~> (PPar {(apply_pattern pat q body), ...rest});

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

        ModCongL . | S ~> T |- (Mod S X) ~> (Mod T X);

        ModCongR . | S ~> T |- (Mod X S) ~> (Mod X T);

        NegIntCong . | S ~> T |- (NegInt S) ~> (NegInt T);
        NegProcCong . | S ~> T |- (NegProc S) ~> (NegProc T);

        BitAndCongL . | S ~> T |- (BitAnd S X) ~> (BitAnd T X);

        BitAndCongR . | S ~> T |- (BitAnd X S) ~> (BitAnd X T);

        BitOrCongL . | S ~> T |- (BitOr S X) ~> (BitOr T X);

        BitOrCongR . | S ~> T |- (BitOr X S) ~> (BitOr X T);

        BitNotCong . | S ~> T |- (BitNot S) ~> (BitNot T);

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
        CastFixedCong . | S ~> T |- (CastFixed S) ~> (CastFixed T);
        FractionProcCongL . | S ~> T |- (FractionProc S X) ~> (FractionProc T X);
        FractionProcCongR . | S ~> T |- (FractionProc X S) ~> (FractionProc X T);
        IntBinProcCongL . | S ~> T |- (IntBinProc S R) ~> (IntBinProc T R);
        IntBinProcCongR . | S ~> T |- (IntBinProc L S) ~> (IntBinProc L T);
        UIntBinProcCongL . | S ~> T |- (UIntBinProc S R) ~> (UIntBinProc T R);
        UIntBinProcCongR . | S ~> T |- (UIntBinProc L S) ~> (UIntBinProc L T);
        FloatBinProcCongL . | S ~> T |- (FloatBinProc S R) ~> (FloatBinProc T R);
        FloatBinProcCongR . | S ~> T |- (FloatBinProc L S) ~> (FloatBinProc L T);
        FixedBinProcCongL . | S ~> T |- (FixedBinProc S R) ~> (FixedBinProc T R);
        FixedBinProcCongR . | S ~> T |- (FixedBinProc L S) ~> (FixedBinProc L T);
        BigintCastProcCong . | S ~> T |- (BigintCastProc S) ~> (BigintCastProc T);
        BigratCastProcCong . | S ~> T |- (BigratCastProc S) ~> (BigratCastProc T);
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
