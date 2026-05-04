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
:: ledtest; #[test] fn parity_ledtest_expr_cross_cat_num_0000()
{
    let input = "0"; let legacy = ledtest :: Expr :: parse(input); let wpds =
    ledtest :: Expr :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_ledtest_expr_cross_cat_pred_0001()
{
    let input = "true"; let legacy = ledtest :: Expr :: parse(input); let wpds
    = ledtest :: Expr :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_ledtest_num_cross_cat_pred_0002()
{
    let input = "true"; let legacy = ledtest :: Num :: parse(input); let wpds
    = ledtest :: Num :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_ledtest_num_infix_plus_0003()
{
    let input = "0 + 0"; let legacy = ledtest :: Num :: parse(input); let wpds
    = ledtest :: Num :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_ledtest_num_infix_star_0004()
{
    let input = "0 * 0"; let legacy = ledtest :: Num :: parse(input); let wpds
    = ledtest :: Num :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_ledtest_pred_infix_eqeq_0005()
{
    let input = "0 == 0"; let legacy = ledtest :: Pred :: parse(input); let
    wpds = ledtest :: Pred :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_ledtest_pred_infix_bangeq_0006()
{
    let input = "0 != 0"; let legacy = ledtest :: Pred :: parse(input); let
    wpds = ledtest :: Pred :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_ledtest_pred_infix_and_0007()
{
    let input = "true and true"; let legacy = ledtest :: Pred :: parse(input);
    let wpds = ledtest :: Pred :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_ledtest_expr_infix_pipe_0008()
{
    let input = "0 | 0"; let legacy = ledtest :: Expr :: parse(input); let
    wpds = ledtest :: Expr :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_ledtest_num_unary_minus_0009()
{
    let input = "- 0"; let legacy = ledtest :: Num :: parse(input); let wpds =
    ledtest :: Num :: parse_via_wpds(input); match (legacy, wpds)
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
} #[test] fn parity_ledtest_num_call_to_num_0010()
{
    let input = "to_num(0)"; let legacy = ledtest :: Num :: parse(input); let
    wpds = ledtest :: Num :: parse_via_wpds(input); match (legacy, wpds)
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