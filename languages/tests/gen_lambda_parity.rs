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
:: lambda; #[test] fn parity_placeholder_no_fixtures() {}