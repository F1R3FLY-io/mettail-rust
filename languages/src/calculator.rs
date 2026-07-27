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
        ![mettail_runtime::CanonicalFixedPoint] as Fixed
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
                // ★ Divergence I, Stage A′ (2026-07-27). The SAME defect this file already
                // fixed for `BigInt` below, in the one integer category it was left in.
                //
                // The eval was `parse_int_lit(text, None)` — a UNIVERSAL ACCEPTOR of every
                // integer spelling — flatly contradicting the MANDATORY `u32` tail its own
                // `pattern` declares one line up. Because a category's literal domain is
                // decided by its `eval` and by nothing else
                // (`macros/src/gen/runtime/wpda_codegen/prefix.rs`, the doc comment on
                // `classify_literal_patterned`), a BARE numeral was a
                // live `UInt32::NumLit` reading:
                //
                //     UInt32::parse("7")  ⇒ Ok(NumLit(7))        ← accepted without the tail
                //     format!("{}", UInt32::NumLit(7)) ⇒ "7u32"  ← written back WITH it
                //
                // Display is right (the pattern says `u32`); the acceptor was wrong. The gap
                // put a term in the SPPF whose display is not the surface it was parsed from,
                // so `"0 + 0"` in a `BigRat` position carried FOUR readings, three displaying
                // `"0 + 0"` and one — `UInt32ToBigRat(AddUInt32 …)` — displaying `"0u32 + 0u32"`.
                // `parse_via_wpda` elects by GLOBAL argmin over whole-derivation
                // `LexicographicWeight` (the generated
                // `__mettail_wpda_select_min_weight_realizing`), so which of the four won was a
                // function of the WHOLE expression: appending a third factor flipped the FIRST
                // factor's carrier, and with it the surface —
                //
                //     "(0 + 0) * 0u32"                     ⇒ IntToBigRat(AddInt …)     surface stable
                //     "(0 + 0) * 0u32 * (0p0 bitand 0p0)"  ⇒ UInt32ToBigRat(AddUInt32 …)
                //                                          ⇒ "(0u32 + 0u32) * 0u32 * …"
                //
                // — which is the `bigrat_display_parse_roundtrip` failure. Fixing the ELECTION
                // would have been fixing the wrong layer: the reading it was electing was one
                // the grammar should never have admitted (`languages/src/rhocalc.rs:129`).
                //
                // The eval now accepts EXACTLY its declared `…u32` domain. Unlike `BigInt`
                // below there is NO superset clause and none is needed: every unsuffixed
                // numeral already has a carrier — `Int` when it fits `i32`, `BigInt` by its
                // overflow clause otherwise — so narrowing here removes readings without
                // removing spellings. The carrier of a numeral is now a function of the
                // numeral TEXT alone, and no remaining reading of a canonical surface
                // RE-SPELLS a token — readings may still differ in the language's inert
                // `(` … `)` grouping, and legitimately do, so that (not display equality)
                // is the invariant pinned by
                // `languages/tests/numeric_literal_carrier_is_text_determined.rs`.
                if matches!(
                    mettail_prattail::IntSuffix::from_text(text),
                    mettail_prattail::IntSuffix::U32
                ) {
                    mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::U32))
                        .map_err(|_| ())
                } else {
                    Err(())
                }
            } ]
        }
        Int {
            // Int (i32) literals; unsuffixed defaults to i32. Leading `-?`
            // No leading `-?`: aligned with main/Rholang (unary minus is an operator,
            // not a signed literal) — merge decision "prefer main's regexes".
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)(i32)?";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::I32)).map_err(|_| ())
            } ]
        }
        BigInt {
            // Required `n` suffix (aligned with main: bare `1` is not a BigInt).
            // Leading `-?` retained for BigInt (matches main's BigInt regex).
            pattern: r"-?(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)n";
            eval: ![ {
                // ★ Divergence I, Stage A (2026-07-25). The comment above says "bare
                // `1` is not a BigInt" — but `parse_int_lit(text, None)` accepted EVERY
                // integer spelling, so bare `1` WAS a BigInt and the declared `n` was
                // decorative. That contradiction is the defect itself: it made
                // `BigInt::parse("0")` succeed, so once Display started emitting the
                // mandatory `n` tail (Stage C) `Display(Parse("0")) = "0n" ≠ "0"` and
                // the roundtrip lost its fixpoint (caught by
                // `gen_calculator_unit::unit_calculator_bigint_{inttobigint,uint32tobigint}`).
                //
                // The eval now accepts EXACTLY its declared `…n` domain, plus the
                // unsuffixed numerals too large for `Int`'s `i32` carrier — the same
                // priority-ordered superset RhoCalc uses, and what kept a bare
                // `3_000_000_000` readable before.
                let __lit = mettail_prattail::parse_int_lit(text, None).map_err(|_| ())?;
                let __declared_bigint = text.ends_with('n');
                let __unsuffixed_overflow = matches!(
                    mettail_prattail::IntSuffix::from_text(text),
                    mettail_prattail::IntSuffix::Unsuffixed
                ) && __lit.as_i64().and_then(|v| i32::try_from(v).ok()).is_none();
                if __declared_bigint || __unsuffixed_overflow {
                    Ok(__lit)
                } else {
                    Err(())
                }
            } ]
        }
        // BigRat sugar: `<int>r` (whole) or `<int>r/<int>r` (composite).
        // C3 (2026-04-28): regex now lexes the composite `1r/2r` form atomically
        // so the rational literal arrives as a single token. Maximal-munch DFA
        // priority: longer match wins, so `1r/2r` does not split into `1r`,`/`,`2r`.
        // Negative-on-second-side (`-1r/-2r`) is intentionally NOT supported —
        // splits into three tokens; users write `-(1r/2r)` for that case.
        BigRat {
            // No leading `-?` (aligned with main); the `Nr/Dr` composite-rational form
            // is THIS branch's superseding feature, retained per merge decision.
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)r(/(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)r)?";
            eval: ![ {
                mettail_prattail::parse_rational_lit(text).map_err(|_| ())
            } ]
        }
        // Before Float: float pattern allows digit runs without `.`/`e`, which would steal `10` from `10p1`.
        Fixed {
            // Scale after `p` is one or more digits: `p1`, `p12`, `p1_0` — not `p` + two-digit-only tail.
            pattern: r"-?([0-9](_?[0-9])*(\.[0-9](_?[0-9])*)?|\.[0-9](_?[0-9])*)p[0-9](_?[0-9])*";
            eval: ![ { mettail_runtime::parse_fixed_lit(text).map_err(|_| ()) } ]
        }
        Float {
            // Decimal or exponent; optional explicit f64 suffix; leading `-` in the token (unary is not split).
            pattern: r"-?([0-9](_?[0-9])*(\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?|[eE][+-]?[0-9](_?[0-9])*)(f64)?|\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?(f64)?)";
            eval: ![ { mettail_runtime::parse_float_lit(text).map_err(|_| ()) } ]
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
        ProcFixed . f:Fixed |- f : Proc ;
        // BigRat error normal form: concrete syntax `error`, not a CanonicalBigRat. Step rules
        // reduce invalid rationals (e.g. fraction with zero denominator) here instead of panicking.
        // The procedural macro keys off the zero-ary `Err` name on BigRat when lowering Fraction.
        Err . |- "error" : BigRat ;
        // Generic arithmetic-error variant for Int (e.g. factorial of negative).
        // The procedural macro routes `None` results from step-rule eval code to
        // this zero-ary `Err` variant — see `macros/src/logic/mod.rs` step emitter.
        Err . |- "error" : Int ;
        CastErrInt . |- "cast_error_int" : Int ;
        CastErrUInt32 . |- "cast_error_uint" : UInt32 ;
        CastErrFixed . |- "cast_error_fixed" : Fixed ;
        CastErrFloat . |- "cast_error_float" : Float ;
        CastErrBigInt . |- "cast_error_bigint" : BigInt ;
        // Int→BigInt / Int→BigRat injection (no body = AST wrapper like ProcInt).
        // Lets bare digits (no `n`/`r` suffix) parse as BigInt / BigRat via
        // cross-cat dispatch, preserving display→parse roundtrip when display
        // is bare.
        IntToBigInt . i:Int |- i : BigInt ;
        IntToBigRat . i:Int |- i : BigRat ;
        // try_from_nd is None when the denominator is zero; the step rule maps that to `Err`.
        Fraction . a:BigInt, b:BigInt |- "fraction" "(" a "," b ")" : BigRat ![{
            mettail_runtime::CanonicalBigRat::try_from_nd(a.get().clone(), b.get().clone())
        }] step;
        AddBigRat . a:BigRat, b:BigRat |- a "+" b : BigRat ![a + b] fold;
        MulBigRat . a:BigRat, b:BigRat |- a "*" b : BigRat ![a * b] fold;
        DivBigRat . a:BigRat, b:BigRat |- a "/" b : BigRat ![a / b] fold;
        NegBigRat . a:BigRat |- "-" a : BigRat ![(-a)] fold;
        BitAndBigRat . a:BigRat, b:BigRat |- a "bitand" b : BigRat ![a.bitand_aligned(b)] fold;
        BitOrBigRat . a:BigRat, b:BigRat |- a "bitor" b : BigRat ![a.bitor_aligned(b)] fold;
        BitNotBigRat . a:BigRat |- "bitnot" a : BigRat ![a.bitnot()] fold;
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
        EqFixed . a:Fixed, b:Fixed |- a "==" b : Bool ![a == b] step;
        GtFixed . a:Fixed, b:Fixed |- a ">" b : Bool ![a > b] step;
        LtFixed . a:Fixed, b:Fixed |- a "<" b : Bool ![a < b] step;
        LtEqFixed . a:Fixed, b:Fixed |- a "<=" b : Bool ![a <= b] step;
        GtEqFixed . a:Fixed, b:Fixed |- a ">=" b : Bool ![a >= b] step;
        NeFixed . a:Fixed, b:Fixed |- a "!=" b : Bool ![a != b] step;
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
        BitAndUInt32 . a:UInt32, b:UInt32 |- a "bitand" b : UInt32 ![a & b] fold;
        BitOrUInt32 . a:UInt32, b:UInt32 |- a "bitor" b : UInt32 ![a | b] fold;
        BitNotUInt32 . a:UInt32 |- "bitnot" a : UInt32 ![!a] fold;
        AddBigInt . a:BigInt, b:BigInt |- a "+" b : BigInt ![a + b] fold;
        SubBigInt . a:BigInt, b:BigInt |- a "-" b : BigInt ![mettail_runtime::CanonicalBigInt::from(a.get() - b.get())] fold;
        NegBigInt . a:BigInt |- "-" a : BigInt ![mettail_runtime::CanonicalBigInt::from(-a.get())] fold;
        BitAndBigInt . a:BigInt, b:BigInt |- a "bitand" b : BigInt ![mettail_runtime::CanonicalBigInt::from(a.get() & b.get())] fold;
        BitOrBigInt . a:BigInt, b:BigInt |- a "bitor" b : BigInt ![mettail_runtime::CanonicalBigInt::from(a.get() | b.get())] fold;
        BitNotBigInt . a:BigInt |- "bitnot" a : BigInt ![mettail_runtime::CanonicalBigInt::from(!a.get())] fold;
        // Int operations
        // Int arithmetic: simple forms — the `language!` macro's `safeify`
        // pass (macros/src/gen/native/rust_code_rewrite.rs) automatically
        // rewrites `+`/`-`/`*`/`/`/`%`/`^`/`.pow()`/`.product()`/unary `-`
        // into `SafeArith`/`SafeFloat` calls that return `None` on overflow
        // or NaN, so we do not need manual `checked_*` invocations here.
        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
        MulInt . a:Int, b:Int |- a "*" b : Int ![a * b] fold;
        DivInt . a:Int, b:Int |- a "/" b : Int ![a / b] fold;
        ModInt . a:Int, b:Int |- a "%" b : Int ![a % b] fold;
        PowInt . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step right;
        BitAndInt . a:Int, b:Int |- a "bitand" b : Int ![a & b] fold;
        BitOrInt . a:Int, b:Int |- a "bitor" b : Int ![a | b] fold;
        BitNotInt . a:Int |- "bitnot" a : Int ![!a] fold;
        Neg . a:Int |- "-" a : Int ![(-a)] fold;
        Fact . a:Int |- a "!" : Int ![{
            // Factorial is undefined for negative integers. Returning `None`
            // here routes the rewrite to `Int::Err` via the HOL step emitter.
            if a < 0 { None } else { Some((1..=a).product::<i32>()) }
        }] step;
        // Float operations
        AddFloat . a:Float, b:Float |- a "+" b : Float ![a + b] fold;
        SubFloat . a:Float, b:Float |- a "-" b : Float ![a - b] fold;
        MulFloat . a:Float, b:Float |- a "*" b : Float ![a * b] fold;
        DivFloat . a:Float, b:Float |- a "/" b : Float ![a / b] fold;
        PowFloat . a:Float, b:Float |- a "^" b : Float ![a.powf(b)] step right;
        NegFloat . a:Float |- "-" a : Float ![{ mettail_runtime::CanonicalFloat64::from(-a.get()) }] fold;
        SinFloat . a:Float |- "sin" "(" a ")" : Float ![a.sin()] step;
        CosFloat . a:Float |- "cos" "(" a ")" : Float ![a.cos()] step;
        ExpFloat . a:Float |- "exp" "(" a ")" : Float ![a.exp()] step;
        LnFloat . a:Float |- "ln" "(" a ")" : Float ![a.ln()] step;
        // Type casts (feature-branch set — simple single-arg forms)
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

        // Fixed-point arithmetic (from main)
        AddFixed . a:Fixed, b:Fixed |- a "+" b : Fixed ![a + b] fold;
        SubFixed . a:Fixed, b:Fixed |- a "-" b : Fixed ![a - b] fold;
        MulFixed . a:Fixed, b:Fixed |- a "*" b : Fixed ![a * b] fold;
        DivFixed . a:Fixed, b:Fixed |- a "/" b : Fixed ![a / b] fold;
        ModFixed . a:Fixed, b:Fixed |- a "%" b : Fixed ![a % b] fold;
        NegFixed . a:Fixed |- "-" a : Fixed ![(-a)] fold;
        BitAndFixed . a:Fixed, b:Fixed |- a "bitand" b : Fixed ![a & b] fold;
        BitOrFixed . a:Fixed, b:Fixed |- a "bitor" b : Fixed ![a | b] fold;
        BitNotFixed . a:Fixed |- "bitnot" a : Fixed ![mettail_runtime::CanonicalFixedPoint::new(!a.unscaled().clone(), a.places())] fold;
    ProcToBool . a:Proc |- "bool" "(" a ")" : Bool ![{
            match a {
                Proc::ProcBool(b) => b.as_ref().eval(),
                Proc::ProcInt(i) => i.as_ref().eval() != 0,
                Proc::ProcUInt32(u) => u.as_ref().eval() != 0,
                Proc::ProcBigInt(n) => !num_traits::Zero::is_zero(n.as_ref().eval().get()),
                Proc::ProcBigRat(r) => !num_traits::Zero::is_zero(r.as_ref().eval().get()),
                Proc::ProcFloat(f) => f.as_ref().eval().get() != 0.0,
                Proc::ProcFixed(x) => !num_traits::Zero::is_zero(x.as_ref().eval().unscaled()),
                Proc::ProcStr(s) => s.as_ref().eval().parse().unwrap_or(false),
                Proc::ElemList(list, index) => {
                    let idx_opt = match index.as_ref() { Int::NumLit(n) => Some(*n as usize), _ => None };
                    let list_opt = match list.as_ref() { List::ListLit(v) => Some(v), _ => None };
                    let elem_opt = idx_opt.and_then(|idx| list_opt.and_then(|v| v.get(idx).cloned()));
                    if let Some(elem) = elem_opt {
                        match &elem {
                            Proc::ProcBool(b) => b.as_ref().eval(),
                            Proc::ProcInt(i) => i.as_ref().eval() != 0,
                            Proc::ProcUInt32(u) => u.as_ref().eval() != 0,
                            Proc::ProcBigInt(n) => !num_traits::Zero::is_zero(n.as_ref().eval().get()),
                            Proc::ProcBigRat(r) => !num_traits::Zero::is_zero(r.as_ref().eval().get()),
                            Proc::ProcFloat(f) => f.as_ref().eval().get() != 0.0,
                            Proc::ProcFixed(x) => !num_traits::Zero::is_zero(x.as_ref().eval().unscaled()),
                            Proc::ProcStr(s) => s.as_ref().eval().parse().unwrap_or(false),
                            _ => false,
                        }
                    } else {
                        false
                    }
                }
                _ => false,
            }
        }] fold;
        // Stage 3.12.9 α-4 (2026-05-04): use fallible `try_eval()` instead of
        // panicking `eval()` for each `Proc::Proc<X>` arm. Combined with β's
        // extended `try_eval` (which handles auto-injection wrappers like
        // `BigRat::IntToBigRat(NumLit(_))`), this preserves functionality
        // for lossless wrappers while gracefully falling to `String::new()`
        // for unevaluable inputs (Var, partially-reduced). The
        // `String::new()` fallback mirrors the existing `_ => String::new()`
        // catch-all at the bottom — same semantics, just per-arm contract
        // correctness instead of waiting for the catch-all.
        ProcToStr . a:Proc |- "str" "(" a ")" : Str ![{
            match a {
                Proc::ProcStr(s) => s.as_ref().eval(),
                Proc::ProcInt(i) => match i.as_ref().try_eval() {
                    Some(v) => v.to_string(),
                    None => String::new(),
                },
                Proc::ProcUInt32(u) => match u.as_ref().try_eval() {
                    Some(v) => v.to_string(),
                    None => String::new(),
                },
                Proc::ProcBigInt(n) => match n.as_ref().try_eval() {
                    Some(v) => v.to_string(),
                    None => String::new(),
                },
                Proc::ProcBigRat(r) => match r.as_ref().try_eval() {
                    Some(v) => v.to_string(),
                    None => String::new(),
                },
                Proc::ProcFloat(f) => match f.as_ref().try_eval() {
                    Some(v) => v.to_string(),
                    None => String::new(),
                },
                Proc::ProcFixed(x) => match x.as_ref().try_eval() {
                    Some(v) => v.to_string(),
                    None => String::new(),
                },
                Proc::ProcBool(b) => match b.as_ref().try_eval() {
                    Some(v) => v.to_string(),
                    None => String::new(),
                },
                Proc::ElemList(list, index) => {
                    let idx_opt = match index.as_ref() { Int::NumLit(n) => Some(*n as usize), _ => None };
                    let list_opt = match list.as_ref() { List::ListLit(v) => Some(v), _ => None };
                    let elem_opt = idx_opt.and_then(|idx| list_opt.and_then(|v| v.get(idx).cloned()));
                    if let Some(elem) = elem_opt {
                        match &elem {
                            Proc::ProcStr(s) => s.as_ref().eval(),
                            Proc::ProcInt(i) => match i.as_ref().try_eval() {
                                Some(v) => v.to_string(),
                                None => String::new(),
                            },
                            Proc::ProcUInt32(u) => match u.as_ref().try_eval() {
                                Some(v) => v.to_string(),
                                None => String::new(),
                            },
                            Proc::ProcBigInt(n) => match n.as_ref().try_eval() {
                                Some(v) => v.to_string(),
                                None => String::new(),
                            },
                            Proc::ProcBigRat(r) => match r.as_ref().try_eval() {
                                Some(v) => v.to_string(),
                                None => String::new(),
                            },
                            Proc::ProcFloat(f) => match f.as_ref().try_eval() {
                                Some(v) => v.to_string(),
                                None => String::new(),
                            },
                            Proc::ProcFixed(x) => match x.as_ref().try_eval() {
                                Some(v) => v.to_string(),
                                None => String::new(),
                            },
                            Proc::ProcBool(b) => match b.as_ref().try_eval() {
                                Some(v) => v.to_string(),
                                None => String::new(),
                            },
                            _ => String::new(),
                        }
                    } else {
                        String::new()
                    }
                }
                _ => String::new(),
            }
        }] fold;
        // Explicit numeric casts (see `docs/design/made/native-types/numeric-casting.md`): binary width required.
        IntBin . a:Proc, w:Int |- "int" "(" a "," w ")" : Int ![{
            mettail_runtime::numeric_int_bin_i32(a, w)
        }] fold;
        UIntBin . a:Proc, w:Int |- "uint" "(" a "," w ")" : UInt32 ![{
            mettail_runtime::numeric_uint_bin_u32(a, w)
        }] fold;
        FloatBin . a:Proc, w:Int |- "float" "(" a "," w ")" : Float ![{
            mettail_runtime::numeric_float_bin(a, w)
        }] fold;
        FixedBin . a:Proc, w:Int |- "fixed" "(" a "," w ")" : Fixed ![{
            mettail_runtime::numeric_fixed_bin(a, w)
        }] fold;
        BigintCast . a:Proc |- "bigint" "(" a ")" : BigInt ![{
            mettail_runtime::numeric_bigint_unary(a)
        }] fold;
        BigratCast . a:Proc |- "bigrat" "(" a ")" : BigRat ![{
            mettail_runtime::numeric_bigrat_unary(a)
        }] fold;
        // List operations (List = Vec<Proc>). Fold/step pass payloads; rust_code returns payload.
        ConcatList . a:List, b:List |- "concat" "(" a "," b ")" : List ![
            { let mut o = a.clone(); o.extend(b.iter().cloned()); o }
        ] fold;
        LenList . a:List |- "length" "(" a ")" : Int ![
            a.len() as i32
        ] fold;
        ElemList . a:List, i:Int |- "at" "(" a "," i ")" : Proc ![
            { let idx_opt: Option<usize> = match &i { Int::NumLit(n) if *n >= 0 => Some(*n as usize), _ => None }; idx_opt.and_then(|idx| a.get(idx).cloned()).expect("ElemList: invalid index") }
        ] fold;
        DeleteList . a:List, i:Int |- "delete" "(" a "," i ")" : List ![
            { let idx_opt: Option<usize> = match &i { Int::NumLit(n) if *n >= 0 => Some(*n as usize), _ => None }; let mut v = a.clone(); match idx_opt { Some(idx) if idx < v.len() => { v.remove(idx); Some(v) }, _ => None }.expect("DeleteList: invalid index") }
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
        EqFixedCongL . | S ~> T |- (EqFixed S R) ~> (EqFixed T R);
        EqFixedCongR . | S ~> T |- (EqFixed L S) ~> (EqFixed L T);
        GtFixedCongL . | S ~> T |- (GtFixed S R) ~> (GtFixed T R);
        GtFixedCongR . | S ~> T |- (GtFixed L S) ~> (GtFixed L T);
        LtFixedCongL . | S ~> T |- (LtFixed S R) ~> (LtFixed T R);
        LtFixedCongR . | S ~> T |- (LtFixed L S) ~> (LtFixed L T);
        LtEqFixedCongL . | S ~> T |- (LtEqFixed S R) ~> (LtEqFixed T R);
        LtEqFixedCongR . | S ~> T |- (LtEqFixed L S) ~> (LtEqFixed L T);
        GtEqFixedCongL . | S ~> T |- (GtEqFixed S R) ~> (GtEqFixed T R);
        GtEqFixedCongR . | S ~> T |- (GtEqFixed L S) ~> (GtEqFixed L T);
        NeFixedCongL . | S ~> T |- (NeFixed S R) ~> (NeFixed T R);
        NeFixedCongR . | S ~> T |- (NeFixed L S) ~> (NeFixed L T);
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
        NegFloatCong . | S ~> T |- (NegFloat S) ~> (NegFloat T);
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
        BitAndIntCongL . | S ~> T |- (BitAndInt S R) ~> (BitAndInt T R);
        BitAndIntCongR . | S ~> T |- (BitAndInt L S) ~> (BitAndInt L T);
        BitOrIntCongL . | S ~> T |- (BitOrInt S R) ~> (BitOrInt T R);
        BitOrIntCongR . | S ~> T |- (BitOrInt L S) ~> (BitOrInt L T);
        BitNotIntCong . | S ~> T |- (BitNotInt S) ~> (BitNotInt T);
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
        AddFixedCongL . | S ~> T |- (AddFixed S R) ~> (AddFixed T R);
        AddFixedCongR . | S ~> T |- (AddFixed L S) ~> (AddFixed L T);
        SubFixedCongL . | S ~> T |- (SubFixed S R) ~> (SubFixed T R);
        SubFixedCongR . | S ~> T |- (SubFixed L S) ~> (SubFixed L T);
        MulFixedCongL . | S ~> T |- (MulFixed S R) ~> (MulFixed T R);
        MulFixedCongR . | S ~> T |- (MulFixed L S) ~> (MulFixed L T);
        DivFixedCongL . | S ~> T |- (DivFixed S R) ~> (DivFixed T R);
        DivFixedCongR . | S ~> T |- (DivFixed L S) ~> (DivFixed L T);
        ModFixedCongL . | S ~> T |- (ModFixed S R) ~> (ModFixed T R);
        ModFixedCongR . | S ~> T |- (ModFixed L S) ~> (ModFixed L T);
        NegFixedCong . | S ~> T |- (NegFixed S) ~> (NegFixed T);
        BitAndFixedCongL . | S ~> T |- (BitAndFixed S R) ~> (BitAndFixed T R);
        BitAndFixedCongR . | S ~> T |- (BitAndFixed L S) ~> (BitAndFixed L T);
        BitOrFixedCongL . | S ~> T |- (BitOrFixed S R) ~> (BitOrFixed T R);
        BitOrFixedCongR . | S ~> T |- (BitOrFixed L S) ~> (BitOrFixed L T);
        BitNotFixedCong . | S ~> T |- (BitNotFixed S) ~> (BitNotFixed T);
        // Proc → concrete type projection congruence
        ProcToBoolCong . | S ~> T |- (ProcToBool S) ~> (ProcToBool T);
        ProcToStrCong . | S ~> T |- (ProcToStr S) ~> (ProcToStr T);
        IntBinCongL . | S ~> T |- (IntBin S R) ~> (IntBin T R);
        IntBinCongR . | S ~> T |- (IntBin L S) ~> (IntBin L T);
        UIntBinCongL . | S ~> T |- (UIntBin S R) ~> (UIntBin T R);
        UIntBinCongR . | S ~> T |- (UIntBin L S) ~> (UIntBin L T);
        FloatBinCongL . | S ~> T |- (FloatBin S R) ~> (FloatBin T R);
        FloatBinCongR . | S ~> T |- (FloatBin L S) ~> (FloatBin L T);
        FixedBinCongL . | S ~> T |- (FixedBin S R) ~> (FixedBin T R);
        FixedBinCongR . | S ~> T |- (FixedBin L S) ~> (FixedBin L T);
        BigintCastCong . | S ~> T |- (BigintCast S) ~> (BigintCast T);
        BigratCastCong . | S ~> T |- (BigratCast S) ~> (BigratCast T);
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
        // Ternary conditional
        TernCongC . | S ~> T |- (Tern S R1 R2) ~> (Tern T R1 R2);
        TernCongT . | S ~> T |- (Tern L S R) ~> (Tern L T R);
        TernCongE . | S ~> T |- (Tern L R S) ~> (Tern L R T);
        // No List/Bag congruence: only Proc congruence (e.g. ProcList/ProcBag) is needed.
        ProcUInt32Cong . | S ~> T |- (ProcUInt32 S) ~> (ProcUInt32 T);
        AddUInt32CongL . | S ~> T |- (AddUInt32 S R) ~> (AddUInt32 T R);
        AddUInt32CongR . | S ~> T |- (AddUInt32 L S) ~> (AddUInt32 L T);
        BitAndUInt32CongL . | S ~> T |- (BitAndUInt32 S R) ~> (BitAndUInt32 T R);
        BitAndUInt32CongR . | S ~> T |- (BitAndUInt32 L S) ~> (BitAndUInt32 L T);
        BitOrUInt32CongL . | S ~> T |- (BitOrUInt32 S R) ~> (BitOrUInt32 T R);
        BitOrUInt32CongR . | S ~> T |- (BitOrUInt32 L S) ~> (BitOrUInt32 L T);
        BitNotUInt32Cong . | S ~> T |- (BitNotUInt32 S) ~> (BitNotUInt32 T);
        ProcBigIntCong . | S ~> T |- (ProcBigInt S) ~> (ProcBigInt T);
        AddBigIntCongL . | S ~> T |- (AddBigInt S R) ~> (AddBigInt T R);
        AddBigIntCongR . | S ~> T |- (AddBigInt L S) ~> (AddBigInt L T);
        SubBigIntCongL . | S ~> T |- (SubBigInt S R) ~> (SubBigInt T R);
        SubBigIntCongR . | S ~> T |- (SubBigInt L S) ~> (SubBigInt L T);
        NegBigIntCong . | S ~> T |- (NegBigInt S) ~> (NegBigInt T);
        BitAndBigIntCongL . | S ~> T |- (BitAndBigInt S R) ~> (BitAndBigInt T R);
        BitAndBigIntCongR . | S ~> T |- (BitAndBigInt L S) ~> (BitAndBigInt L T);
        BitOrBigIntCongL . | S ~> T |- (BitOrBigInt S R) ~> (BitOrBigInt T R);
        BitOrBigIntCongR . | S ~> T |- (BitOrBigInt L S) ~> (BitOrBigInt L T);
        BitNotBigIntCong . | S ~> T |- (BitNotBigInt S) ~> (BitNotBigInt T);
        ProcBigRatCong . | S ~> T |- (ProcBigRat S) ~> (ProcBigRat T);
        ProcFixedCong . | S ~> T |- (ProcFixed S) ~> (ProcFixed T);
        FractionCongN . | S ~> T |- (Fraction S R) ~> (Fraction T R);
        FractionCongD . | S ~> T |- (Fraction L S) ~> (Fraction L T);
        AddBigRatCongL . | S ~> T |- (AddBigRat S R) ~> (AddBigRat T R);
        AddBigRatCongR . | S ~> T |- (AddBigRat L S) ~> (AddBigRat L T);
        BitAndBigRatCongL . | S ~> T |- (BitAndBigRat S R) ~> (BitAndBigRat T R);
        BitAndBigRatCongR . | S ~> T |- (BitAndBigRat L S) ~> (BitAndBigRat L T);
        BitOrBigRatCongL . | S ~> T |- (BitOrBigRat S R) ~> (BitOrBigRat T R);
        BitOrBigRatCongR . | S ~> T |- (BitOrBigRat L S) ~> (BitOrBigRat L T);
        BitNotBigRatCong . | S ~> T |- (BitNotBigRat S) ~> (BitNotBigRat T);
        MulBigRatCongL . | S ~> T |- (MulBigRat S R) ~> (MulBigRat T R);
        MulBigRatCongR . | S ~> T |- (MulBigRat L S) ~> (MulBigRat L T);
        DivBigRatCongL . | S ~> T |- (DivBigRat S R) ~> (DivBigRat T R);
        DivBigRatCongR . | S ~> T |- (DivBigRat L S) ~> (DivBigRat L T);
        NegBigRatCong . | S ~> T |- (NegBigRat S) ~> (NegBigRat T);

        // Cast-propagation congruences: let `str(2^3)` reduce its inner
        // operand to a literal before the cast fires. Without these, nested
        // expressions inside casts reach no normal form.
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
    },
}
