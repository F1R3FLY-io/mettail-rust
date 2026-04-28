# ! [allow(non_snake_case, unused_imports, dead_code)] # !
[doc = r" Auto-generated Phase 9 Model A parity tests."] # ! [doc = r""] # !
[doc = r" For each grammar shape (atomic literal, terminal keyword,"] # !
[doc = r" cross-cat projection, infix, prefix, function call, collection),"] #
! [doc = r" calls both the trampoline `Cat::parse(input)` and the WPDS"] # !
[doc = r" `Cat::parse_via_wpds(input)`, asserting the two parse paths"] # !
[doc = r" produce equal AST values via PartialEq. Divergences where one"] # !
[doc = r" backend succeeds and the other fails are surfaced as test"] # !
[doc = r" failures; per `feedback_parity_drift_ok_if_better.md`, accepted"] #
! [doc = r" divergences should be moved out of this generator into a"] # !
[doc = r" WPDS-only or trampoline-only fixture file."] use mettail_languages
:: rhocalc; #[test] fn parity_rhocalc_int_atomic_lit_0000()
{
    let input = "0"; let legacy = rhocalc :: Int :: parse(input); let wpds =
    rhocalc :: Int :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_int_atomic_lit_0001()
{
    let input = "1"; let legacy = rhocalc :: Int :: parse(input); let wpds =
    rhocalc :: Int :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_int_atomic_lit_0002()
{
    let input = "42"; let legacy = rhocalc :: Int :: parse(input); let wpds =
    rhocalc :: Int :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_int_atomic_lit_0003()
{
    let input = "-1"; let legacy = rhocalc :: Int :: parse(input); let wpds =
    rhocalc :: Int :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_int_atomic_lit_0004()
{
    let input = "1000"; let legacy = rhocalc :: Int :: parse(input); let wpds
    = rhocalc :: Int :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_uint32_atomic_lit_0005()
{
    let input = "0u32"; let legacy = rhocalc :: UInt32 :: parse(input); let
    wpds = rhocalc :: UInt32 :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_uint32_atomic_lit_0006()
{
    let input = "1u32"; let legacy = rhocalc :: UInt32 :: parse(input); let
    wpds = rhocalc :: UInt32 :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_uint32_atomic_lit_0007()
{
    let input = "42u32"; let legacy = rhocalc :: UInt32 :: parse(input); let
    wpds = rhocalc :: UInt32 :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_uint32_atomic_lit_0008()
{
    let input = "100u32"; let legacy = rhocalc :: UInt32 :: parse(input); let
    wpds = rhocalc :: UInt32 :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigint_atomic_lit_0009()
{
    let input = "0n"; let legacy = rhocalc :: BigInt :: parse(input); let wpds
    = rhocalc :: BigInt :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigint_atomic_lit_0010()
{
    let input = "1n"; let legacy = rhocalc :: BigInt :: parse(input); let wpds
    = rhocalc :: BigInt :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigint_atomic_lit_0011()
{
    let input = "42n"; let legacy = rhocalc :: BigInt :: parse(input); let
    wpds = rhocalc :: BigInt :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigint_atomic_lit_0012()
{
    let input = "1000n"; let legacy = rhocalc :: BigInt :: parse(input); let
    wpds = rhocalc :: BigInt :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigrat_atomic_lit_0013()
{
    let input = "0r"; let legacy = rhocalc :: BigRat :: parse(input); let wpds
    = rhocalc :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigrat_atomic_lit_0014()
{
    let input = "1r"; let legacy = rhocalc :: BigRat :: parse(input); let wpds
    = rhocalc :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigrat_atomic_lit_0015()
{
    let input = "42r"; let legacy = rhocalc :: BigRat :: parse(input); let
    wpds = rhocalc :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigrat_atomic_lit_0016()
{
    let input = "100r"; let legacy = rhocalc :: BigRat :: parse(input); let
    wpds = rhocalc :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigrat_atomic_lit_0017()
{
    let input = "1r/2r"; let legacy = rhocalc :: BigRat :: parse(input); let
    wpds = rhocalc :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigrat_atomic_lit_0018()
{
    let input = "3r/4r"; let legacy = rhocalc :: BigRat :: parse(input); let
    wpds = rhocalc :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigrat_atomic_lit_0019()
{
    let input = "0r/1r"; let legacy = rhocalc :: BigRat :: parse(input); let
    wpds = rhocalc :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigrat_atomic_lit_0020()
{
    let input = "10r/100r"; let legacy = rhocalc :: BigRat :: parse(input);
    let wpds = rhocalc :: BigRat :: parse_via_wpds(input); match
    (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bigrat_atomic_lit_0021()
{
    let input = "0xFr/0x2r"; let legacy = rhocalc :: BigRat :: parse(input);
    let wpds = rhocalc :: BigRat :: parse_via_wpds(input); match
    (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_fixed_atomic_lit_0022()
{
    let input = "1.5p2"; let legacy = rhocalc :: Fixed :: parse(input); let
    wpds = rhocalc :: Fixed :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_fixed_atomic_lit_0023()
{
    let input = "0.5p2"; let legacy = rhocalc :: Fixed :: parse(input); let
    wpds = rhocalc :: Fixed :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_fixed_atomic_lit_0024()
{
    let input = "3.14p2"; let legacy = rhocalc :: Fixed :: parse(input); let
    wpds = rhocalc :: Fixed :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_float_atomic_lit_0025()
{
    let input = "0.0"; let legacy = rhocalc :: Float :: parse(input); let wpds
    = rhocalc :: Float :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_float_atomic_lit_0026()
{
    let input = "1.0"; let legacy = rhocalc :: Float :: parse(input); let wpds
    = rhocalc :: Float :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_float_atomic_lit_0027()
{
    let input = "3.14"; let legacy = rhocalc :: Float :: parse(input); let
    wpds = rhocalc :: Float :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_float_atomic_lit_0028()
{
    let input = "2.5e1"; let legacy = rhocalc :: Float :: parse(input); let
    wpds = rhocalc :: Float :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_float_atomic_lit_0029()
{
    let input = "-1.5"; let legacy = rhocalc :: Float :: parse(input); let
    wpds = rhocalc :: Float :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_term_kw_0030()
{
    let input = "{}"; let legacy = rhocalc :: Proc :: parse(input); let wpds =
    rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_term_kw_0031()
{
    let input = "error"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_cross_cat_bigrat_0032()
{
    let input = "0r"; let legacy = rhocalc :: Proc :: parse(input); let wpds =
    rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_cross_cat_fixed_0033()
{
    let input = "1.5p2"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_cross_cat_float_0034()
{
    let input = "0.0"; let legacy = rhocalc :: Proc :: parse(input); let wpds
    = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_cross_cat_bigint_0035()
{
    let input = "0n"; let legacy = rhocalc :: Proc :: parse(input); let wpds =
    rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_cross_cat_uint32_0036()
{
    let input = "0u32"; let legacy = rhocalc :: Proc :: parse(input); let wpds
    = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_cross_cat_int_0037()
{
    let input = "0"; let legacy = rhocalc :: Proc :: parse(input); let wpds =
    rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_cross_cat_bool_0038()
{
    let input = "true"; let legacy = rhocalc :: Proc :: parse(input); let wpds
    = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_cross_cat_str_0039()
{
    let input = "\"hello\""; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_or_0040()
{
    let input = "{} or {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_and_0041()
{
    let input = "{} and {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_bitor_0042()
{
    let input = "{} bitor {}"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_bitand_0043()
{
    let input = "{} bitand {}"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_eqeq_0044()
{
    let input = "{} == {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_bangeq_0045()
{
    let input = "{} != {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_gt_0046()
{
    let input = "{} > {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_lt_0047()
{
    let input = "{} < {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_gteq_0048()
{
    let input = "{} >= {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_lteq_0049()
{
    let input = "{} <= {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_plus_0050()
{
    let input = "{} + {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_minus_0051()
{
    let input = "{} - {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_star_0052()
{
    let input = "{} * {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_slash_0053()
{
    let input = "{} / {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_infix_percent_0054()
{
    let input = "{} % {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_int_unary_minus_0055()
{
    let input = "- 0"; let legacy = rhocalc :: Int :: parse(input); let wpds =
    rhocalc :: Int :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_unary_bitnot_0056()
{
    let input = "bitnot {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_unary_minus_0057()
{
    let input = "- {}"; let legacy = rhocalc :: Proc :: parse(input); let wpds
    = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_unary_not_0058()
{
    let input = "not {}"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_name_call___0059()
{
    let input = "@({})"; let legacy = rhocalc :: Name :: parse(input); let
    wpds = rhocalc :: Name :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_int_0060()
{
    let input = "int({}, 0)"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_uint_0061()
{
    let input = "uint({}, 0)"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_float_0062()
{
    let input = "float({}, 0)"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_fixed_0063()
{
    let input = "fixed({}, 0)"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_bigint_0064()
{
    let input = "bigint({})"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_bigrat_0065()
{
    let input = "bigrat({})"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_fraction_0066()
{
    let input = "fraction({}, {})"; let legacy = rhocalc :: Proc ::
    parse(input); let wpds = rhocalc :: Proc :: parse_via_wpds(input); match
    (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_concat_0067()
{
    let input = "concat({}, {})"; let legacy = rhocalc :: Proc ::
    parse(input); let wpds = rhocalc :: Proc :: parse_via_wpds(input); match
    (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_at_0068()
{
    let input = "at({}, {})"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_delete_0069()
{
    let input = "delete({}, {})"; let legacy = rhocalc :: Proc ::
    parse(input); let wpds = rhocalc :: Proc :: parse_via_wpds(input); match
    (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_union_0070()
{
    let input = "union({}, {})"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_remove_0071()
{
    let input = "remove({}, {})"; let legacy = rhocalc :: Proc ::
    parse(input); let wpds = rhocalc :: Proc :: parse_via_wpds(input); match
    (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_diff_0072()
{
    let input = "diff({}, {})"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_int_call_count_0073()
{
    let input = "count({}, {})"; let legacy = rhocalc :: Int :: parse(input);
    let wpds = rhocalc :: Int :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_get_0074()
{
    let input = "get({}, {})"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_put_0075()
{
    let input = "put({}, {}, {})"; let legacy = rhocalc :: Proc ::
    parse(input); let wpds = rhocalc :: Proc :: parse_via_wpds(input); match
    (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_mapdelete_0076()
{
    let input = "mapdelete({}, {})"; let legacy = rhocalc :: Proc ::
    parse(input); let wpds = rhocalc :: Proc :: parse_via_wpds(input); match
    (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_merge_0077()
{
    let input = "merge({}, {})"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_has_0078()
{
    let input = "has({}, {})"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_keys_0079()
{
    let input = "keys({})"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_values_0080()
{
    let input = "values({})"; let legacy = rhocalc :: Proc :: parse(input);
    let wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_len_0081()
{
    let input = "len({})"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_bool_0082()
{
    let input = "bool({})"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_proc_call_str_0083()
{
    let input = "str({})"; let legacy = rhocalc :: Proc :: parse(input); let
    wpds = rhocalc :: Proc :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bag_coll_empty_0084()
{
    let input = "{}"; let legacy = rhocalc :: Bag :: parse(input); let wpds =
    rhocalc :: Bag :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bag_coll_single_0085()
{
    let input = "{ {} }"; let legacy = rhocalc :: Bag :: parse(input); let
    wpds = rhocalc :: Bag :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_bag_coll_multi_0086()
{
    let input = "{ {} | {} }"; let legacy = rhocalc :: Bag :: parse(input);
    let wpds = rhocalc :: Bag :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_map_coll_empty_0087()
{
    let input = "{}"; let legacy = rhocalc :: Map :: parse(input); let wpds =
    rhocalc :: Map :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_map_coll_single_0088()
{
    let input = "{ {} }"; let legacy = rhocalc :: Map :: parse(input); let
    wpds = rhocalc :: Map :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_rhocalc_map_coll_multi_0089()
{
    let input = "{ {} , {} }"; let legacy = rhocalc :: Map :: parse(input);
    let wpds = rhocalc :: Map :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
}