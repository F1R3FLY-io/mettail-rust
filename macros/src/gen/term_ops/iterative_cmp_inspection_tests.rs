//! Executable leaf-control projections, not a complete comparison inspector.
use super::*;
use crate::gen::term_ops::iterative_hash::checked_tests::fixture_language;

fn compact(tokens: TokenStream) -> String {
    tokens.to_string().split_whitespace().collect()
}

#[test]
fn inspected_leaf_controls_do_not_invent_results_or_execute_comparisons() {
    let inspection = CmpEmissionNames::inspect_contributions();
    for (fragment, operation) in [
        (inspection.native_ne_guard(quote! { left }, quote! { right }), "ne"),
        (inspection.native_cmp_guard(quote! { left }, quote! { right }), "cmp"),
        (inspection.native_cmp_verdict(quote! { left }, quote! { right }), "cmp"),
    ] {
        syn::parse2::<syn::Block>(fragment.clone()).expect("inspection block syntax");
        let source = compact(fragment);
        assert!(
            source.contains(&format!("::try_inspect_native_{operation}_work(left,right,reserve)?"))
        );
        assert!(source.contains("state.try_accumulate_parts(__comparison_work,0,0,reserve)"));
        for forbidden in ["try_native_", "Ordering::", "return", "Verdict", "stack.push", "if"] {
            assert!(!source.contains(forbidden), "unexpected {forbidden}: {source}");
        }
    }
}

#[test]
fn existing_leaf_execution_fragments_retain_exact_tokens() {
    for emission in [CmpEmissionNames::ordinary(), CmpEmissionNames::checked()] {
        let different = emission.native_ne(quote! { left }, quote! { right });
        let return_false = emission.return_value(quote! { false });
        assert_eq!(
            compact(emission.native_ne_guard(quote! { left }, quote! { right })),
            compact(quote! { if #different { #return_false } }),
        );
        let order = emission.native_cmp(quote! { left }, quote! { right });
        let return_order = emission.return_value(quote! { ord });
        assert_eq!(
            compact(emission.native_cmp_guard(quote! { left }, quote! { right })),
            compact(quote! {
                let ord = #order;
                if ord != std::cmp::Ordering::Equal { #return_order }
            }),
        );
        let task_enum = &emission.task_enum;
        let push = emission.push_task(quote! { #task_enum::Verdict(#order) });
        assert_eq!(
            compact(emission.native_cmp_verdict(quote! { left }, quote! { right })),
            compact(quote! { #push; }),
        );
    }
}

#[test]
#[should_panic(expected = "leaf contributions do not provide a complete Eq inspector")]
fn leaf_projection_cannot_be_exposed_as_a_complete_eq_engine() {
    generate_eq_engine(
        &fixture_language(),
        &CmpEmissionNames::inspect_contributions(),
    );
}

#[test]
#[should_panic(expected = "leaf contributions do not provide a complete Ord inspector")]
fn leaf_projection_cannot_be_exposed_as_a_complete_ord_engine() {
    generate_cmp_engine(
        &fixture_language(),
        &CmpEmissionNames::inspect_contributions(),
    );
}

#[test]
fn leaf_inspection_captures_original_generated_fragments_for_execution() {
    let inspection = CmpEmissionNames::inspect_contributions();
    let cases = [
        (
            "check_ne",
            quote! { mettail_runtime::CheckedNativeEqualityLeaf },
            format_ident!("try_inspect_native_ne_work"),
            inspection.native_ne_guard(quote! { left }, quote! { right }),
        ),
        (
            "check_cmp_guard",
            quote! { mettail_runtime::CheckedNativeOrderingLeaf },
            format_ident!("try_inspect_native_cmp_work"),
            inspection.native_cmp_guard(quote! { left }, quote! { right }),
        ),
        (
            "check_cmp_verdict",
            quote! { mettail_runtime::CheckedNativeOrderingLeaf },
            format_ident!("try_inspect_native_cmp_work"),
            inspection.native_cmp_verdict(quote! { left }, quote! { right }),
        ),
    ];
    let functions = cases.into_iter().map(|(name, bound, method, fragment)| {
        let name = format_ident!("{name}");
        quote! {
            fn #name<T: #bound>(left: &T, right: &T) {
                let expected = left.#method(right, &mut |_, _| Ok::<_, usize>(()))
                    .expect("fixture metadata allowance");
                for limit in 0usize..=2 {
                    let initial = BindingCharge::new(7, 2, 3).expect("fixture charge");
                    let mut state = initial;
                    let mut trace = Vec::new();
                    let mut calls = 0;
                    let reserve = &mut |work, units| {
                        trace.push((work, units));
                        calls += 1;
                        if calls > limit { Err(limit) } else { Ok(()) }
                    };
                    let result: Result<(), NativeComparisonFailure<usize>> = (|| {
                        #fragment
                        Ok(())
                    })();
                    if limit < 2 {
                        assert_eq!(result, Err(NativeComparisonFailure::Admission(
                            BindingFailure::Reservation(limit))));
                        assert_eq!(state, initial, "refusal cannot publish a partial sum");
                        assert_eq!(trace, vec![(1, 0); limit + 1]);
                    } else {
                        assert_eq!(result, Ok(()));
                        assert_eq!(trace, [(1, 0), (1, 0)]);
                        assert_eq!(state.base_work(), 7 + expected);
                        assert_eq!(state.records(), 2);
                        assert_eq!(state.owned_bytes(), 3);
                    }
                }
                let initial = BindingCharge::new(usize::MAX, 0, 0).expect("maximal work fits");
                let mut state = initial;
                let mut trace = Vec::new();
                let reserve = &mut |work, units| { trace.push((work, units)); Ok::<_, usize>(()) };
                let overflow: Result<(), NativeComparisonFailure<usize>> = (|| {
                    #fragment
                    Ok(())
                })();
                assert_eq!(overflow, Err(NativeComparisonFailure::Admission(BindingFailure::SizeOverflow)));
                assert_eq!(state, initial);
                assert_eq!(trace, [(1, 0), (1, 0)]);

                let mut state = BindingCharge::ZERO;
                let mut trace = Vec::new();
                let reserve = &mut |work, units| { trace.push((work, units)); Ok::<_, usize>(()) };
                let continuation: Result<(), NativeComparisonFailure<usize>> = (|| {
                    #fragment
                    #fragment
                    Ok(())
                })();
                assert_eq!(continuation, Ok(()), "unknown comparison must not stop inspection");
                assert_eq!(state.base_work(), 2 * expected);
                assert_eq!(trace, [(1, 0); 4]);
            }
        }
    });
    let fixture = quote! {
        use mettail_runtime::{Binder, FreeVar, BindingFailure, NativeComparisonFailure};
        use mettail_runtime::binding_receipt::BindingCharge;
        #(#functions)*
        fn main() {
            check_ne(&-42i64, &19i64);
            check_cmp_guard(&-42i64, &19i64);
            check_cmp_verdict(&-42i64, &19i64);
            check_ne(&true, &false);
            check_cmp_guard(&true, &false);
            check_cmp_verdict(&true, &false);
            let left = "alpha".repeat(1000);
            let right = "beta".repeat(1000);
            check_ne(&left, &right);
            check_cmp_guard(&left, &right);
            check_cmp_verdict(&left, &right);
            check_ne(&left, &left);
            check_cmp_guard(&left, &left);
            check_cmp_verdict(&left, &left);
            let binder = Binder(FreeVar::fresh_named("x".to_owned()));
            let other = Binder(FreeVar::fresh_named("x".to_owned()));
            check_ne(&binder, &other);
            check_ne(&vec![binder.clone()], &vec![other.clone()]);
            check_ne(&vec![binder], &vec![other.clone(), other]);
            println!("generated Ne, eager Cmp and deferred Cmp metadata fragments pass every reservation cut");
        }
    };
    syn::parse2::<syn::File>(fixture.clone()).expect("leaf inspection executable syntax");
    if std::env::var_os("METTAIL_CAPTURE_CHECKED_CMP").is_some() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/verification/cmp-emitter");
        std::fs::create_dir_all(&directory).expect("create comparison fixture directory");
        std::fs::write(directory.join("leaf-contributions.rs"), fixture.to_string())
            .expect("capture actual leaf-control fragments");
    }
}
