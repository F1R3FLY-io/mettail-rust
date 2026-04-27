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
:: importedmath; #[test] fn parity_importedmath_num_infix_plus_0000()
{
    let input = "0 + 0"; let legacy = importedmath :: Num :: parse(input); let
    wpds = importedmath :: Num :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_importedmath_num_infix_minus_0001()
{
    let input = "0 - 0"; let legacy = importedmath :: Num :: parse(input); let
    wpds = importedmath :: Num :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
            input, a, we,);
        } (Err(le), Ok(b)) =>
        {
            panic!
            ("Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
            input, b, le,);
        }
    }
} #[test] fn parity_importedmath_num_infix_slash_0002()
{
    let input = "0 / 0"; let legacy = importedmath :: Num :: parse(input); let
    wpds = importedmath :: Num :: parse_via_wpds(input); match (legacy, wpds)
    {
        (Ok(a), Ok(b)) =>
        {
            assert_eq!
            (a, b, "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
            input, a, b,);
        } (Err(le), Err(we)) => { let _ = (le, we); } (Ok(a), Err(we)) =>
        {
            panic!
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