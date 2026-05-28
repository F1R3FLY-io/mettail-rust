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
            // Leading `-?` preserves atomic negative lexing — efficiency (no runtime negation).
            pattern: r"-?(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)(i64)?";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::I64)).map_err(|_| ())
            } ]
        }
        BigInt {
            pattern: r"-?(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)n?";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
            } ]
        }
        BigRat {
            pattern: r"-?(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)r?";
            eval: ![ {
                mettail_prattail::parse_rational_lit(text).map_err(|_| ())
            } ]
        }
        Fixed {
            pattern: r"-?([0-9](_?[0-9])*(\.[0-9](_?[0-9])*)?|\.[0-9](_?[0-9])*)p[0-9](_?[0-9])*";
            eval: ![ { mettail_runtime::parse_fixed_lit(text).map_err(|_| ()) } ]
        }
        Float {
            pattern: r"-?([0-9](_?[0-9])*(\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?|[eE][+-]?[0-9](_?[0-9])*)(f64)?|\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?(f64)?)";
            eval: ![ { mettail_runtime::parse_float_lit(text).map_err(|_| ()) } ]
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
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(na), Some(nb)) => {
                        match mettail_runtime::CanonicalBigRat::try_from_nd(na.get().clone(), nb.get().clone()) {
                            Some(r) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(r))),
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
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(*x || *y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        And . a:Proc, b:Proc |- a "and" b : Proc ![
            { match (&a, &b) {
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(*x && *y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        // Bitwise (looser precedence than arithmetic)
        // Use `bitor` (not `|`) so `{ P | Q }` stays parallel composition (PPar separator).
        BitOr . a:Proc, b:Proc |- a "bitor" b : Proc ![
            { match (&a, &b) {
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(x | y))),
                    _ => Proc::Err,
                },
                (Proc::CastInt(a), Proc::CastInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(x | y))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x | y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() | y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(x.bitor_aligned(y)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        BitAnd . a:Proc, b:Proc |- a "bitand" b : Proc ![
            { match (&a, &b) {
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(x & y))),
                    _ => Proc::Err,
                },
                (Proc::CastInt(a), Proc::CastInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(x & y))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x & y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() & y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(x.bitand_aligned(y)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        BitNot . a:Proc |- "bitnot" a : Proc ![
            { match &a {
                Proc::CastInt(x) => match x.as_ref().try_eval() {
                    Some(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(!v))),
                    _ => Proc::Err,
                },
                Proc::CastUInt32(x) => match x.as_ref().try_eval() {
                    Some(v) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(!v))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match x.as_ref().try_eval() {
                    Some(n) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(!n.get())))),
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match x.as_ref().try_eval() {
                    Some(r) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(r.bitnot()))),
                    _ => Proc::Err,
                },
                Proc::CastFixed(x) => match x.as_ref().try_eval() {
                    Some(fp) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(
                        mettail_runtime::CanonicalFixedPoint::new(!fp.unscaled().clone(), fp.places()),
                    ))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Eq . a:Proc, b:Proc |- a "==" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x == y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x == y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Ne . a:Proc, b:Proc |- a "!=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x != y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x != y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Gt . a:Proc, b:Proc |- a ">" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x > y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x > y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Lt . a:Proc, b:Proc |- a "<" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x < y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x < y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        GtEq . a:Proc, b:Proc |- a ">=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x >= y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x >= y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        LtEq . a:Proc, b:Proc |- a "<=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(i), Some(j)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x <= y))),
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(x <= y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        // Arithmetic (tighter than == and and/or)
        Add . a:Proc, b:Proc |- a "+" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(std::sync::Arc::new((**a).clone()+ (**b).clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x + y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() + y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(x + y))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(std::sync::Arc::new((**a).clone()+ (**b).clone())),
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(x + y))),
                    _ => Proc::Err,
                },
                (Proc::CastStr(a), Proc::CastStr(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(format!("{}{}", x, y)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Sub . a:Proc, b:Proc |- a "-" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(std::sync::Arc::new((**a).clone()- (**b).clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x - y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() - y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(x - y))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(std::sync::Arc::new((**a).clone()- (**b).clone())),
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(x - y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Mul . a:Proc, b:Proc |- a "*" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(std::sync::Arc::new((**a).clone()* (**b).clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x * y))),
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() * y.get())))),
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(x * y))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(std::sync::Arc::new((**a).clone()* (**b).clone())),
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(x * y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Div . a:Proc, b:Proc |- a "/" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(std::sync::Arc::new((**a).clone()/ (**b).clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => {
                        if y == 0 { Proc::Err } else { Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x / y))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => {
                        if y.get().is_zero() { Proc::Err } else { Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() / y.get())))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => {
                        if y.get().is_zero() { Proc::Err } else { Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(x / y))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(std::sync::Arc::new((**a).clone()/ (**b).clone())),
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => {
                        match x.checked_div(y) {
                            Some(q) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(q))),
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
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(std::sync::Arc::new((**a).clone()% (**b).clone())),
                (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => {
                        if y == 0 { Proc::Err } else { Proc::CastUInt32(std::sync::Arc::new(UInt32::NumLit(x % y))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => {
                        if y.get().is_zero() { Proc::Err } else { Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(x.get() % y.get())))) }
                    }
                    _ => Proc::Err,
                },
                (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref().try_eval(), b.as_ref().try_eval()) {
                    (Some(x), Some(y)) => {
                        match x.checked_rem(y) {
                            Some(r) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(r))),
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
                Proc::CastInt(x) => match x.as_ref().try_eval() {
                    Some(n) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(-n))),
                    _ => Proc::Err,
                },
                Proc::CastUInt32(x) => match x.as_ref().try_eval() {
                    Some(u) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(-(u as i64)))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match x.as_ref().try_eval() {
                    Some(n) => Proc::CastBigInt(std::sync::Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(-n.get())))),
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match x.as_ref().try_eval() {
                    Some(r) => Proc::CastBigRat(std::sync::Arc::new(BigRat::RatLit(r.neg()))),
                    _ => Proc::Err,
                },
                Proc::CastFloat(x) => match x.as_ref().try_eval() {
                    Some(f) => Proc::CastFloat(std::sync::Arc::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(-f.get())))),
                    _ => Proc::Err,
                },
                Proc::CastFixed(x) => match x.as_ref().try_eval() {
                    Some(fp) => Proc::CastFixed(std::sync::Arc::new(Fixed::FixedLit(fp.neg()))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        // List operations: take Proc, match CastList/ListLit in semantic (like arithmetic)
        ConcatList . a:Proc, b:Proc |- "concat" "(" a "," b ")" : Proc ![
            { match (&a, &b) {
                (Proc::CastList(la), Proc::CastList(lb)) => match (la.as_ref(), lb.as_ref()) {
                    (List::ListLit(va), List::ListLit(vb)) => { let mut o = va.clone(); o.extend(vb.iter().cloned()); Proc::CastList(std::sync::Arc::new(List::ListLit(o))) },
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
                    (List::ListLit(v), Int::NumLit(n)) => { let idx = *n as usize; let mut vec = v.clone(); if idx >= vec.len() { panic!("delete: index out of bounds"); } vec.remove(idx); Proc::CastList(std::sync::Arc::new(List::ListLit(vec))) },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        // Bag operations: take Proc, match CastBag/BagLit in semantic (like arithmetic)
        UnionBag . a:Proc, b:Proc |- "union" "(" a "," b ")" : Proc ![
            { match (&a, &b) {
                (Proc::CastBag(ba), Proc::CastBag(bb)) => match (ba.as_ref(), bb.as_ref()) {
                    (Bag::BagLit(ha), Bag::BagLit(hb)) => Proc::CastBag(std::sync::Arc::new(Bag::BagLit(ha.union(hb)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        RemoveBag . a:Proc, e:Proc |- "remove" "(" a "," e ")" : Proc ![
            { match &a {
                Proc::CastBag(b) => match b.as_ref() { Bag::BagLit(h) => Proc::CastBag(std::sync::Arc::new(Bag::BagLit(h.remove_one(&e)))), _ => Proc::Err },
                _ => Proc::Err,
            }}
        ] fold;
        DiffBag . a:Proc, b:Proc |- "diff" "(" a "," b ")" : Proc ![
            { match (&a, &b) {
                (Proc::CastBag(ba), Proc::CastBag(bb)) => match (ba.as_ref(), bb.as_ref()) {
                    (Bag::BagLit(ha), Bag::BagLit(hb)) => Proc::CastBag(std::sync::Arc::new(Bag::BagLit(ha.diff(hb)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        // Fix B follow-up (2026-05-11): replaced `panic!()` fallbacks with
        // `0i64` (a silent total fallback). The prior `panic!` paths were
        // unreachable before the fusion engine fix at `fusion.rs:754`
        // (committed alongside this change) — that fix legitimately fires
        // CountBag's fold rule on subterm-decomposed `Proc::Err`
        // arguments, which would panic the runtime. A fold body must be
        // total. Int (the result type) has no `Err` variant, so the
        // safe fallback is 0 — callers consume the count as an i64 and
        // 0 is a sentinel-safe value for "no matches" / "type mismatch".
        CountBag . b:Proc, e:Proc |- "count" "(" b "," e ")" : Int ![
            { match &b {
                Proc::CastBag(bag) => match bag.as_ref() {
                    Bag::BagLit(h) => mettail_runtime::HashBag::count(h, &e) as i64,
                    _ => 0i64,
                },
                _ => 0i64,
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
                        Proc::CastMap(std::sync::Arc::new(Map::MapLit(new_map)))
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
                        Proc::CastMap(std::sync::Arc::new(Map::MapLit(new_map)))
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
                        Proc::CastMap(std::sync::Arc::new(Map::MapLit(m)))
                    },
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        HasMap . m:Proc, k:Proc |- "has" "(" m "," k ")" : Proc ![
            { match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(payload.get(&k).is_some()))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        KeysMap . m:Proc |- "keys" "(" m ")" : Proc ![
            { match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => Proc::CastList(std::sync::Arc::new(List::ListLit(payload.iter().map(|(k, _)| k.clone()).collect::<Vec<_>>()))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;
        ValuesMap . m:Proc |- "values" "(" m ")" : Proc ![
            { match &m {
                Proc::CastMap(inner) => match inner.as_ref() {
                    Map::MapLit(ref payload) => Proc::CastList(std::sync::Arc::new(List::ListLit(payload.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>()))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Not . a:Proc |- "not" a : Proc ![
            { match &a {
                Proc::CastBool(b) => match b.as_ref().try_eval() {
                    Some(v) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(!v))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Len . p:Proc |- "len" "(" p ")" : Proc ![
            { match &p {
                Proc::CastStr(inner) => match inner.as_ref().try_eval() {
                    Some(x) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(x.len() as i64))),
                    _ => Proc::Err,
                },
                Proc::CastList(l) => match l.as_ref().try_eval() {
                    Some(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v.len() as i64))),
                    _ => Proc::Err,
                },
                Proc::CastMap(m) => match m.as_ref().try_eval() {
                    Some(payload) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(payload.len() as i64))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        ToBool . p:Proc |- "bool" "(" p ")" : Proc ![
            { match &p {
                Proc::CastBool(x) => Proc::CastBool(x.clone()),
                Proc::CastInt(x) => match x.as_ref().try_eval() {
                    Some(i) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(i != 0))),
                    _ => Proc::Err,
                },
                Proc::CastUInt32(x) => match x.as_ref().try_eval() {
                    Some(u) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(u != 0))),
                    _ => Proc::Err,
                },
                Proc::CastBigInt(x) => match x.as_ref().try_eval() {
                    Some(n) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(!n.get().is_zero()))),
                    _ => Proc::Err,
                },
                Proc::CastBigRat(x) => match x.as_ref().try_eval() {
                    Some(r) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(!r.get().is_zero()))),
                    _ => Proc::Err,
                },
                Proc::CastFloat(x) => match x.as_ref().try_eval() {
                    Some(f) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(f.get() != 0.0))),
                    _ => Proc::Err,
                },
                Proc::CastFixed(x) => match x.as_ref().try_eval() {
                    Some(fp) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(!Zero::is_zero(fp.unscaled())))),
                    _ => Proc::Err,
                },
                Proc::CastStr(x) => match x.as_ref().try_eval() {
                    Some(s) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(s.parse::<bool>().unwrap_or(false)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        // Stage 3.12.9 α-3 (2026-05-04): use fallible `try_eval()` instead of
        // panicking `eval()` for each `Proc::Cast<X>` arm. Combined with β's
        // extended `try_eval` (which handles auto-injection wrappers like
        // `BigRat::FloatToBigRat(FloatLit(_))`), this preserves functionality
        // for lossless wrappers (`str(2.0)` → `"2"`) while gracefully falling
        // to `Proc::Err` for unevaluable inputs (Var, partially-reduced).
        // Mirrors `ToBool`'s defensive pattern (above, lines 761-794) but uses
        // `try_eval()` instead of literal-pattern-match — strictly more
        // capable since β-extended `try_eval` covers both literals and
        // auto-injection wrappers around literals.
        ToStr . p:Proc |- "str" "(" p ")" : Proc ![
            { match &p {
                Proc::CastStr(x) => Proc::CastStr(x.clone()),
                Proc::CastInt(x) => match x.as_ref().try_eval() {
                    Some(v) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(v.to_string()))),
                    None => Proc::Err,
                },
                Proc::CastUInt32(x) => match x.as_ref().try_eval() {
                    Some(v) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(v.to_string()))),
                    None => Proc::Err,
                },
                Proc::CastBigInt(x) => match x.as_ref().try_eval() {
                    Some(v) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(v.to_string()))),
                    None => Proc::Err,
                },
                Proc::CastBigRat(x) => match x.as_ref().try_eval() {
                    Some(v) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(v.to_string()))),
                    None => Proc::Err,
                },
                Proc::CastFloat(x) => match x.as_ref().try_eval() {
                    Some(v) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(v.to_string()))),
                    None => Proc::Err,
                },
                Proc::CastFixed(x) => match x.as_ref().try_eval() {
                    Some(v) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(v.to_string()))),
                    None => Proc::Err,
                },
                Proc::CastBool(x) => match x.as_ref().try_eval() {
                    Some(v) => Proc::CastStr(std::sync::Arc::new(Str::StringLit(v.to_string()))),
                    None => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;


    },

    equations {
        QuoteDrop . |- (NQuote (PDrop N)) = N ;

        ExecEq . |- (PDrop (NQuote P)) = P ;

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

        // Phase 1 (2026-05-16): removed `path`, `path_vec`, `trans` relations.
        // All three had zero downstream consumers: `run_ascent` result
        // extraction (`runtime/src/language.rs:330-343`) reads only
        // `proc` / `rw_proc` / `eq_proc` via AscentResults.normal_forms /
        // rewrites_from; `trans`'s sole reader was the commented-out
        // `garbage` relation; `path` was read only by `trans`; `path_vec`
        // had no consumer at all (kept historically per commit 94250ed as
        // a syntactic demo that the macro parser handles `relation(Vec<T>)`).
        // The `path_vec` self-concatenation rule (`path_vec(zs) <-- path_vec(xs),
        // path_vec(ys), if xs.last() == ys.first(), ...`) was mathematically
        // unbounded: any rw_proc graph with dense joins produced strictly-
        // growing Vec<Proc> facts ([a,b,c] + [a,b,c] → [a,b,c,b,c] → ...).
        // Empirically this caused 8 GB OOM in ~6 min on `{1+2+3}` reducer
        // tests (chained_add, grouped_mul, str_of_add, str_of_eq,
        // str_of_zero_gt_zero). The author's own TODO comment at the (now
        // removed) `shrinking_path` stub acknowledged the issue.
        //
        // Future direction: if shrinking-step semantics are wanted, the
        // principled implementation is `shrink_step(p,q) <-- rw_proc(p,q),
        // if p.to_string().len() > q.to_string().len()` — bounded by
        // |rw_proc|, no transitive Vec<Proc> accumulation.

        // contexts for testing (TODO: auto-generate)
        // proc(p) <-- if let Ok(p) = Proc::parse("^x.{{ x | serv!(req) }}");
        // proc(p) <-- if let Ok(p) = Proc::parse("^x.{x}");

        // rules to add c(p) to the set of processes
        proc(res) <--
            step_term(p), proc(c),
            if let Proc::LamProc(_) = c,
            let app = Proc::ApplyProc(std::sync::Arc::new(c.clone()), std::sync::Arc::new(p.clone())),
            let res = app.normalize();
        proc(res) <--
            step_term(p), proc(c),
            if let Proc::MLamProc(_) = c,
            let app = Proc::MApplyProc(std::sync::Arc::new(c.clone()), vec![p.clone()]),
            let res = app.normalize();

        // relation garbage(Name,Proc);
        // garbage(n,p) <--
        //     proc(p),name(n),
        //     !(proc(k), trans(p,k,q), can_comm(q,n));
    },
}
