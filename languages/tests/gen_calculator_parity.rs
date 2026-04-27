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
:: calculator; #[test] fn parity_calculator_int_atomic_lit_0000()
{
    let input = "0"; let legacy = calculator :: Int :: parse(input); let wpds
    = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_atomic_lit_0001()
{
    let input = "1"; let legacy = calculator :: Int :: parse(input); let wpds
    = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_atomic_lit_0002()
{
    let input = "42"; let legacy = calculator :: Int :: parse(input); let wpds
    = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_atomic_lit_0003()
{
    let input = "-1"; let legacy = calculator :: Int :: parse(input); let wpds
    = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_atomic_lit_0004()
{
    let input = "-7"; let legacy = calculator :: Int :: parse(input); let wpds
    = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_atomic_lit_0005()
{
    let input = "127"; let legacy = calculator :: Int :: parse(input); let
    wpds = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_uint32_atomic_lit_0006()
{
    let input = "0u32"; let legacy = calculator :: UInt32 :: parse(input); let
    wpds = calculator :: UInt32 :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_uint32_atomic_lit_0007()
{
    let input = "1u32"; let legacy = calculator :: UInt32 :: parse(input); let
    wpds = calculator :: UInt32 :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_uint32_atomic_lit_0008()
{
    let input = "42u32"; let legacy = calculator :: UInt32 :: parse(input);
    let wpds = calculator :: UInt32 :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_uint32_atomic_lit_0009()
{
    let input = "100u32"; let legacy = calculator :: UInt32 :: parse(input);
    let wpds = calculator :: UInt32 :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bigint_atomic_lit_0010()
{
    let input = "0n"; let legacy = calculator :: BigInt :: parse(input); let
    wpds = calculator :: BigInt :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigint_atomic_lit_0011()
{
    let input = "1n"; let legacy = calculator :: BigInt :: parse(input); let
    wpds = calculator :: BigInt :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigint_atomic_lit_0012()
{
    let input = "42n"; let legacy = calculator :: BigInt :: parse(input); let
    wpds = calculator :: BigInt :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigint_atomic_lit_0013()
{
    let input = "1000n"; let legacy = calculator :: BigInt :: parse(input);
    let wpds = calculator :: BigInt :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bigrat_atomic_lit_0014()
{
    let input = "0r"; let legacy = calculator :: BigRat :: parse(input); let
    wpds = calculator :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigrat_atomic_lit_0015()
{
    let input = "1r"; let legacy = calculator :: BigRat :: parse(input); let
    wpds = calculator :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigrat_atomic_lit_0016()
{
    let input = "42r"; let legacy = calculator :: BigRat :: parse(input); let
    wpds = calculator :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigrat_atomic_lit_0017()
{
    let input = "100r"; let legacy = calculator :: BigRat :: parse(input); let
    wpds = calculator :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_atomic_lit_0018()
{
    let input = "1.5p2"; let legacy = calculator :: Fixed :: parse(input); let
    wpds = calculator :: Fixed :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_atomic_lit_0019()
{
    let input = "0.5p2"; let legacy = calculator :: Fixed :: parse(input); let
    wpds = calculator :: Fixed :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_atomic_lit_0020()
{
    let input = "3.14p2"; let legacy = calculator :: Fixed :: parse(input);
    let wpds = calculator :: Fixed :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_float_atomic_lit_0021()
{
    let input = "0.0"; let legacy = calculator :: Float :: parse(input); let
    wpds = calculator :: Float :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_float_atomic_lit_0022()
{
    let input = "1.0"; let legacy = calculator :: Float :: parse(input); let
    wpds = calculator :: Float :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_float_atomic_lit_0023()
{
    let input = "3.14"; let legacy = calculator :: Float :: parse(input); let
    wpds = calculator :: Float :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_float_atomic_lit_0024()
{
    let input = "2.5e1"; let legacy = calculator :: Float :: parse(input); let
    wpds = calculator :: Float :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_float_atomic_lit_0025()
{
    let input = "-1.5"; let legacy = calculator :: Float :: parse(input); let
    wpds = calculator :: Float :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_atomic_lit_0026()
{
    let input = "true"; let legacy = calculator :: Bool :: parse(input); let
    wpds = calculator :: Bool :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_atomic_lit_0027()
{
    let input = "false"; let legacy = calculator :: Bool :: parse(input); let
    wpds = calculator :: Bool :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_str_atomic_lit_0028()
{
    let input = "\"hello\""; let legacy = calculator :: Str :: parse(input);
    let wpds = calculator :: Str :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_str_atomic_lit_0029()
{
    let input = "\"\""; let legacy = calculator :: Str :: parse(input); let
    wpds = calculator :: Str :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_str_atomic_lit_0030()
{
    let input = "\"x\""; let legacy = calculator :: Str :: parse(input); let
    wpds = calculator :: Str :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigrat_term_kw_0031()
{
    let input = "error"; let legacy = calculator :: BigRat :: parse(input);
    let wpds = calculator :: BigRat :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_int_term_kw_0032()
{
    let input = "error"; let legacy = calculator :: Int :: parse(input); let
    wpds = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_term_kw_0033()
{
    let input = "cast_error_int"; let legacy = calculator :: Int ::
    parse(input); let wpds = calculator :: Int :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_uint32_term_kw_0034()
{
    let input = "cast_error_uint"; let legacy = calculator :: UInt32 ::
    parse(input); let wpds = calculator :: UInt32 :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_term_kw_0035()
{
    let input = "cast_error_fixed"; let legacy = calculator :: Fixed ::
    parse(input); let wpds = calculator :: Fixed :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_float_term_kw_0036()
{
    let input = "cast_error_float"; let legacy = calculator :: Float ::
    parse(input); let wpds = calculator :: Float :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bigint_term_kw_0037()
{
    let input = "cast_error_bigint"; let legacy = calculator :: BigInt ::
    parse(input); let wpds = calculator :: BigInt :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_proc_cross_cat_int_0038()
{
    let input = "0"; let legacy = calculator :: Proc :: parse(input); let wpds
    = calculator :: Proc :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_proc_cross_cat_float_0039()
{
    let input = "0.0"; let legacy = calculator :: Proc :: parse(input); let
    wpds = calculator :: Proc :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_proc_cross_cat_bool_0040()
{
    let input = "true"; let legacy = calculator :: Proc :: parse(input); let
    wpds = calculator :: Proc :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_proc_cross_cat_str_0041()
{
    let input = "\"hello\""; let legacy = calculator :: Proc :: parse(input);
    let wpds = calculator :: Proc :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_proc_cross_cat_uint32_0042()
{
    let input = "0u32"; let legacy = calculator :: Proc :: parse(input); let
    wpds = calculator :: Proc :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_proc_cross_cat_bigint_0043()
{
    let input = "0n"; let legacy = calculator :: Proc :: parse(input); let
    wpds = calculator :: Proc :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_proc_cross_cat_bigrat_0044()
{
    let input = "0r"; let legacy = calculator :: Proc :: parse(input); let
    wpds = calculator :: Proc :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_proc_cross_cat_fixed_0045()
{
    let input = "1.5p2"; let legacy = calculator :: Proc :: parse(input); let
    wpds = calculator :: Proc :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigint_cross_cat_int_0046()
{
    let input = "0"; let legacy = calculator :: BigInt :: parse(input); let
    wpds = calculator :: BigInt :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigrat_cross_cat_int_0047()
{
    let input = "0"; let legacy = calculator :: BigRat :: parse(input); let
    wpds = calculator :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigrat_infix_plus_0048()
{
    let input = "0r + 0r"; let legacy = calculator :: BigRat :: parse(input);
    let wpds = calculator :: BigRat :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bigrat_infix_star_0049()
{
    let input = "0r * 0r"; let legacy = calculator :: BigRat :: parse(input);
    let wpds = calculator :: BigRat :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bigrat_infix_slash_0050()
{
    let input = "0r / 0r"; let legacy = calculator :: BigRat :: parse(input);
    let wpds = calculator :: BigRat :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bigrat_infix_bitand_0051()
{
    let input = "0r bitand 0r"; let legacy = calculator :: BigRat ::
    parse(input); let wpds = calculator :: BigRat :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bigrat_infix_bitor_0052()
{
    let input = "0r bitor 0r"; let legacy = calculator :: BigRat ::
    parse(input); let wpds = calculator :: BigRat :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_eqeq_0053()
{
    let input = "0 == 0"; let legacy = calculator :: Bool :: parse(input); let
    wpds = calculator :: Bool :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_eqeq_0054()
{
    let input = "0.0 == 0.0"; let legacy = calculator :: Bool :: parse(input);
    let wpds = calculator :: Bool :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bool_infix_eqeq_0055()
{
    let input = "true == true"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_eqeq_0056()
{
    let input = "\"hello\" == \"hello\""; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_gt_0057()
{
    let input = "0 > 0"; let legacy = calculator :: Bool :: parse(input); let
    wpds = calculator :: Bool :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_gt_0058()
{
    let input = "0.0 > 0.0"; let legacy = calculator :: Bool :: parse(input);
    let wpds = calculator :: Bool :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bool_infix_gt_0059()
{
    let input = "true > true"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_gt_0060()
{
    let input = "\"hello\" > \"hello\""; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_lt_0061()
{
    let input = "0 < 0"; let legacy = calculator :: Bool :: parse(input); let
    wpds = calculator :: Bool :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_lt_0062()
{
    let input = "0.0 < 0.0"; let legacy = calculator :: Bool :: parse(input);
    let wpds = calculator :: Bool :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bool_infix_lt_0063()
{
    let input = "true < true"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_lt_0064()
{
    let input = "\"hello\" < \"hello\""; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_lteq_0065()
{
    let input = "0 <= 0"; let legacy = calculator :: Bool :: parse(input); let
    wpds = calculator :: Bool :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_lteq_0066()
{
    let input = "0.0 <= 0.0"; let legacy = calculator :: Bool :: parse(input);
    let wpds = calculator :: Bool :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bool_infix_lteq_0067()
{
    let input = "true <= true"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_lteq_0068()
{
    let input = "\"hello\" <= \"hello\""; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_gteq_0069()
{
    let input = "0 >= 0"; let legacy = calculator :: Bool :: parse(input); let
    wpds = calculator :: Bool :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_gteq_0070()
{
    let input = "0.0 >= 0.0"; let legacy = calculator :: Bool :: parse(input);
    let wpds = calculator :: Bool :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bool_infix_gteq_0071()
{
    let input = "true >= true"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_gteq_0072()
{
    let input = "\"hello\" >= \"hello\""; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_bangeq_0073()
{
    let input = "0 != 0"; let legacy = calculator :: Bool :: parse(input); let
    wpds = calculator :: Bool :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_bangeq_0074()
{
    let input = "0.0 != 0.0"; let legacy = calculator :: Bool :: parse(input);
    let wpds = calculator :: Bool :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bool_infix_bangeq_0075()
{
    let input = "true != true"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_bangeq_0076()
{
    let input = "\"hello\" != \"hello\""; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_eqeq_0077()
{
    let input = "1.5p2 == 1.5p2"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_gt_0078()
{
    let input = "1.5p2 > 1.5p2"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_lt_0079()
{
    let input = "1.5p2 < 1.5p2"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_lteq_0080()
{
    let input = "1.5p2 <= 1.5p2"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_gteq_0081()
{
    let input = "1.5p2 >= 1.5p2"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_bangeq_0082()
{
    let input = "1.5p2 != 1.5p2"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_and_0083()
{
    let input = "true and true"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_or_0084()
{
    let input = "true or true"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_infix_xor_0085()
{
    let input = "true xor true"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_str_infix_plusplus_0086()
{
    let input = "\"hello\" ++ \"hello\""; let legacy = calculator :: Str ::
    parse(input); let wpds = calculator :: Str :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_str_infix_plus_0087()
{
    let input = "\"hello\" + \"hello\""; let legacy = calculator :: Str ::
    parse(input); let wpds = calculator :: Str :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_uint32_infix_plus_0088()
{
    let input = "0u32 + 0u32"; let legacy = calculator :: UInt32 ::
    parse(input); let wpds = calculator :: UInt32 :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_uint32_infix_bitand_0089()
{
    let input = "0u32 bitand 0u32"; let legacy = calculator :: UInt32 ::
    parse(input); let wpds = calculator :: UInt32 :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_uint32_infix_bitor_0090()
{
    let input = "0u32 bitor 0u32"; let legacy = calculator :: UInt32 ::
    parse(input); let wpds = calculator :: UInt32 :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bigint_infix_plus_0091()
{
    let input = "0n + 0n"; let legacy = calculator :: BigInt :: parse(input);
    let wpds = calculator :: BigInt :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bigint_infix_minus_0092()
{
    let input = "0n - 0n"; let legacy = calculator :: BigInt :: parse(input);
    let wpds = calculator :: BigInt :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bigint_infix_bitand_0093()
{
    let input = "0n bitand 0n"; let legacy = calculator :: BigInt ::
    parse(input); let wpds = calculator :: BigInt :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bigint_infix_bitor_0094()
{
    let input = "0n bitor 0n"; let legacy = calculator :: BigInt ::
    parse(input); let wpds = calculator :: BigInt :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_int_infix_plus_0095()
{
    let input = "0 + 0"; let legacy = calculator :: Int :: parse(input); let
    wpds = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_infix_minus_0096()
{
    let input = "0 - 0"; let legacy = calculator :: Int :: parse(input); let
    wpds = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_infix_star_0097()
{
    let input = "0 * 0"; let legacy = calculator :: Int :: parse(input); let
    wpds = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_infix_slash_0098()
{
    let input = "0 / 0"; let legacy = calculator :: Int :: parse(input); let
    wpds = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_infix_percent_0099()
{
    let input = "0 % 0"; let legacy = calculator :: Int :: parse(input); let
    wpds = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_infix_caret_0100()
{
    let input = "0 ^ 0"; let legacy = calculator :: Int :: parse(input); let
    wpds = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_infix_bitand_0101()
{
    let input = "0 bitand 0"; let legacy = calculator :: Int :: parse(input);
    let wpds = calculator :: Int :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_int_infix_bitor_0102()
{
    let input = "0 bitor 0"; let legacy = calculator :: Int :: parse(input);
    let wpds = calculator :: Int :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_float_infix_plus_0103()
{
    let input = "0.0 + 0.0"; let legacy = calculator :: Float :: parse(input);
    let wpds = calculator :: Float :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_float_infix_minus_0104()
{
    let input = "0.0 - 0.0"; let legacy = calculator :: Float :: parse(input);
    let wpds = calculator :: Float :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_float_infix_star_0105()
{
    let input = "0.0 * 0.0"; let legacy = calculator :: Float :: parse(input);
    let wpds = calculator :: Float :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_float_infix_slash_0106()
{
    let input = "0.0 / 0.0"; let legacy = calculator :: Float :: parse(input);
    let wpds = calculator :: Float :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_float_infix_caret_0107()
{
    let input = "0.0 ^ 0.0"; let legacy = calculator :: Float :: parse(input);
    let wpds = calculator :: Float :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_int_infix_tilde_0108()
{
    let input = "0 ~ 0"; let legacy = calculator :: Int :: parse(input); let
    wpds = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_infix_plus_0109()
{
    let input = "1.5p2 + 1.5p2"; let legacy = calculator :: Fixed ::
    parse(input); let wpds = calculator :: Fixed :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_infix_minus_0110()
{
    let input = "1.5p2 - 1.5p2"; let legacy = calculator :: Fixed ::
    parse(input); let wpds = calculator :: Fixed :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_infix_star_0111()
{
    let input = "1.5p2 * 1.5p2"; let legacy = calculator :: Fixed ::
    parse(input); let wpds = calculator :: Fixed :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_infix_slash_0112()
{
    let input = "1.5p2 / 1.5p2"; let legacy = calculator :: Fixed ::
    parse(input); let wpds = calculator :: Fixed :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_infix_percent_0113()
{
    let input = "1.5p2 % 1.5p2"; let legacy = calculator :: Fixed ::
    parse(input); let wpds = calculator :: Fixed :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_infix_bitand_0114()
{
    let input = "1.5p2 bitand 1.5p2"; let legacy = calculator :: Fixed ::
    parse(input); let wpds = calculator :: Fixed :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_infix_bitor_0115()
{
    let input = "1.5p2 bitor 1.5p2"; let legacy = calculator :: Fixed ::
    parse(input); let wpds = calculator :: Fixed :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bigrat_unary_minus_0116()
{
    let input = "- 0r"; let legacy = calculator :: BigRat :: parse(input); let
    wpds = calculator :: BigRat :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigrat_unary_bitnot_0117()
{
    let input = "bitnot 0r"; let legacy = calculator :: BigRat ::
    parse(input); let wpds = calculator :: BigRat :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_unary_not_0118()
{
    let input = "not true"; let legacy = calculator :: Bool :: parse(input);
    let wpds = calculator :: Bool :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_uint32_unary_bitnot_0119()
{
    let input = "bitnot 0u32"; let legacy = calculator :: UInt32 ::
    parse(input); let wpds = calculator :: UInt32 :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bigint_unary_minus_0120()
{
    let input = "- 0n"; let legacy = calculator :: BigInt :: parse(input); let
    wpds = calculator :: BigInt :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bigint_unary_bitnot_0121()
{
    let input = "bitnot 0n"; let legacy = calculator :: BigInt ::
    parse(input); let wpds = calculator :: BigInt :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_int_unary_bitnot_0122()
{
    let input = "bitnot 0"; let legacy = calculator :: Int :: parse(input);
    let wpds = calculator :: Int :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_int_unary_minus_0123()
{
    let input = "- 0"; let legacy = calculator :: Int :: parse(input); let
    wpds = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_float_unary_minus_0124()
{
    let input = "- 0.0"; let legacy = calculator :: Float :: parse(input); let
    wpds = calculator :: Float :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_unary_minus_0125()
{
    let input = "- 1.5p2"; let legacy = calculator :: Fixed :: parse(input);
    let wpds = calculator :: Fixed :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_fixed_unary_bitnot_0126()
{
    let input = "bitnot 1.5p2"; let legacy = calculator :: Fixed ::
    parse(input); let wpds = calculator :: Fixed :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bigrat_call_fraction_0127()
{
    let input = "fraction(0n, 0n)"; let legacy = calculator :: BigRat ::
    parse(input); let wpds = calculator :: BigRat :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_float_call_sin_0128()
{
    let input = "sin(0.0)"; let legacy = calculator :: Float :: parse(input);
    let wpds = calculator :: Float :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_float_call_cos_0129()
{
    let input = "cos(0.0)"; let legacy = calculator :: Float :: parse(input);
    let wpds = calculator :: Float :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_float_call_exp_0130()
{
    let input = "exp(0.0)"; let legacy = calculator :: Float :: parse(input);
    let wpds = calculator :: Float :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_float_call_ln_0131()
{
    let input = "ln(0.0)"; let legacy = calculator :: Float :: parse(input);
    let wpds = calculator :: Float :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_float_call_float_0132()
{
    let input = "float(0)"; let legacy = calculator :: Float :: parse(input);
    let wpds = calculator :: Float :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_float_call_float_0133()
{
    let input = "float(true)"; let legacy = calculator :: Float ::
    parse(input); let wpds = calculator :: Float :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_float_call_float_0134()
{
    let input = "float(\"hello\")"; let legacy = calculator :: Float ::
    parse(input); let wpds = calculator :: Float :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_int_call_int_0135()
{
    let input = "int(0.0)"; let legacy = calculator :: Int :: parse(input);
    let wpds = calculator :: Int :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_int_call_int_0136()
{
    let input = "int(true)"; let legacy = calculator :: Int :: parse(input);
    let wpds = calculator :: Int :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_int_call_int_0137()
{
    let input = "int(\"hello\")"; let legacy = calculator :: Int ::
    parse(input); let wpds = calculator :: Int :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_str_call_str_0138()
{
    let input = "str(true)"; let legacy = calculator :: Str :: parse(input);
    let wpds = calculator :: Str :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_str_call_str_0139()
{
    let input = "str(0)"; let legacy = calculator :: Str :: parse(input); let
    wpds = calculator :: Str :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_str_call_str_0140()
{
    let input = "str(0.0)"; let legacy = calculator :: Str :: parse(input);
    let wpds = calculator :: Str :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bool_call_bool_0141()
{
    let input = "bool(0)"; let legacy = calculator :: Bool :: parse(input);
    let wpds = calculator :: Bool :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bool_call_bool_0142()
{
    let input = "bool(0.0)"; let legacy = calculator :: Bool :: parse(input);
    let wpds = calculator :: Bool :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bool_call_bool_0143()
{
    let input = "bool(\"hello\")"; let legacy = calculator :: Bool ::
    parse(input); let wpds = calculator :: Bool :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_int_call_int_0144()
{
    let input = "int(0)"; let legacy = calculator :: Int :: parse(input); let
    wpds = calculator :: Int :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_float_call_float_0145()
{
    let input = "float(0.0)"; let legacy = calculator :: Float ::
    parse(input); let wpds = calculator :: Float :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bool_call_bool_0146()
{
    let input = "bool(true)"; let legacy = calculator :: Bool :: parse(input);
    let wpds = calculator :: Bool :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_str_call_str_0147()
{
    let input = "str(\"hello\")"; let legacy = calculator :: Str ::
    parse(input); let wpds = calculator :: Str :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_bool_call_bool_0148()
{
    let input = "bool(0)"; let legacy = calculator :: Bool :: parse(input);
    let wpds = calculator :: Bool :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_str_call_str_0149()
{
    let input = "str(0)"; let legacy = calculator :: Str :: parse(input); let
    wpds = calculator :: Str :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_int_call_int_0150()
{
    let input = "int(0, 0)"; let legacy = calculator :: Int :: parse(input);
    let wpds = calculator :: Int :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_uint32_call_uint_0151()
{
    let input = "uint(0, 0)"; let legacy = calculator :: UInt32 ::
    parse(input); let wpds = calculator :: UInt32 :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_float_call_float_0152()
{
    let input = "float(0, 0)"; let legacy = calculator :: Float ::
    parse(input); let wpds = calculator :: Float :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_fixed_call_fixed_0153()
{
    let input = "fixed(0, 0)"; let legacy = calculator :: Fixed ::
    parse(input); let wpds = calculator :: Fixed :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bigint_call_bigint_0154()
{
    let input = "bigint(0)"; let legacy = calculator :: BigInt ::
    parse(input); let wpds = calculator :: BigInt :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bigrat_call_bigrat_0155()
{
    let input = "bigrat(0)"; let legacy = calculator :: BigRat ::
    parse(input); let wpds = calculator :: BigRat :: parse_via_wpds(input);
    match (legacy, wpds)
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
} #[test] fn parity_calculator_bag_coll_empty_0156()
{
    let input = "{}"; let legacy = calculator :: Bag :: parse(input); let wpds
    = calculator :: Bag :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bag_coll_single_0157()
{
    let input = "{ 0 }"; let legacy = calculator :: Bag :: parse(input); let
    wpds = calculator :: Bag :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_bag_coll_multi_0158()
{
    let input = "{ 0 | 0 }"; let legacy = calculator :: Bag :: parse(input);
    let wpds = calculator :: Bag :: parse_via_wpds(input); match
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
} #[test] fn parity_calculator_map_coll_empty_0159()
{
    let input = "{}"; let legacy = calculator :: Map :: parse(input); let wpds
    = calculator :: Map :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_map_coll_single_0160()
{
    let input = "{ 0 }"; let legacy = calculator :: Map :: parse(input); let
    wpds = calculator :: Map :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_calculator_map_coll_multi_0161()
{
    let input = "{ 0 , 0 }"; let legacy = calculator :: Map :: parse(input);
    let wpds = calculator :: Map :: parse_via_wpds(input); match
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
}