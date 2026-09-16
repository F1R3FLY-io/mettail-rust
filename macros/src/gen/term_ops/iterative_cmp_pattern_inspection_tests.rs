use super::*;

fn compact(tokens: TokenStream) -> String {
    tokens.to_string().split_whitespace().collect()
}

#[test]
fn pattern_inspection_emits_only_metadata_and_checked_accumulation() {
    let emission = CmpEmissionNames::inspect_contributions();
    for (multi, name) in [(false, "single"), (true, "multi")] {
        let fragment = emission.pattern_order(quote! { left }, quote! { right }, multi);
        syn::parse2::<syn::Block>(fragment.clone()).expect("pattern inspection syntax");
        let source = compact(fragment);
        assert!(source.contains(&format!(
            "inspect_generated_{name}_pattern_order_work(left,right,reserve)?"
        )));
        assert!(source.contains(
            "inspect_cmp_scaled_contribution(&mutstate,__comparison_work,0,0,factor,reserve,)?"
        ));
        for forbidden in
            ["pat_ord", "hash_pat", "Hasher", "Hash::", "Ordering::", "Verdict", "return"]
        {
            assert!(!source.contains(forbidden), "unexpected {forbidden}: {source}");
        }
    }
}

#[test]
fn original_pattern_order_tokens_are_preserved() {
    for emission in [CmpEmissionNames::ordinary(), CmpEmissionNames::checked()] {
        let single_precharge = emission.pattern_order_precharge(
            quote! { &l_scope.unsafe_pattern },
            quote! { &r_scope.unsafe_pattern },
            false,
        );
        assert_eq!(
            compact(emission.pattern_order(
                quote! { &l_scope.unsafe_pattern },
                quote! { &r_scope.unsafe_pattern },
                false,
            )),
            compact(quote! {
                #single_precharge
                let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                    let mut h = std::collections::hash_map::DefaultHasher::new();
                    std::hash::Hash::hash(p, &mut h);
                    std::hash::Hasher::finish(&h)
                };
                let pat_ord =
                    hash_pat(&l_scope.unsafe_pattern).cmp(&hash_pat(&r_scope.unsafe_pattern));
            }),
        );
        let multi_precharge =
            emission.pattern_order_precharge(quote! { l_pats }, quote! { r_pats }, true);
        assert_eq!(
            compact(emission.pattern_order(quote! { l_pats }, quote! { r_pats }, true)),
            compact(quote! {
                #multi_precharge
                let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                    let mut h = std::collections::hash_map::DefaultHasher::new();
                    std::hash::Hash::hash(p, &mut h);
                    std::hash::Hasher::finish(&h)
                };
                let pat_ord = l_pats.len().cmp(&r_pats.len()).then_with(|| {
                    l_pats.iter().zip(r_pats.iter())
                        .map(|(lp, rp)| hash_pat(lp).cmp(&hash_pat(rp)))
                        .find(|o| *o != std::cmp::Ordering::Equal)
                        .unwrap_or(std::cmp::Ordering::Equal)
                });
            }),
        );
    }
}

#[test]
fn pattern_inspection_captures_original_fragments_for_execution() {
    let emission = CmpEmissionNames::inspect_contributions();
    let scaled_helper = CmpEmissionNames::inspect_scaled_accumulation_helper();
    let functions = [false, true].into_iter().map(|multi| {
        let name = format_ident!("check_{}", if multi { "multi" } else { "single" });
        let ty = if multi {
            quote! { Vec<Binder<String>> }
        } else {
            quote! { Binder<String> }
        };
        let fragment = emission.pattern_order(quote! { left }, quote! { right }, multi);
        quote! {
            fn #name(left: &#ty, right: &#ty, expected: usize) {
                let factor = 1usize;
                for limit in 0usize..=3 {
                    let initial = BindingCharge::new(7, 2, 3).expect("populated fixture charge");
                    let mut state = initial;
                    let mut trace = Vec::new();
                    let reserve = &mut |work, units| {
                        trace.push((work, units));
                        if trace.len() > limit { Err(limit) } else { Ok(()) }
                    };
                    let result: Result<(), NativeComparisonFailure<usize>> = (|| {
                        #fragment
                        Ok(())
                    })();
                    if limit < 3 {
                        assert_eq!(result, Err(NativeComparisonFailure::Admission(
                            BindingFailure::Reservation(limit))));
                        assert_eq!(state, initial);
                        assert_eq!(trace, vec![(1, 0); limit + 1]);
                    } else {
                        assert_eq!(result, Ok(()));
                        assert_eq!(trace, [(1, 0); 3]);
                        assert_eq!(state.base_work(), 7 + expected);
                        assert_eq!(state.records(), 2);
                        assert_eq!(state.owned_bytes(), 3);
                    }
                }
            }
        }
    });
    let fixture = quote! {
        use mettail_runtime::{Binder, FreeVar, BindingFailure, NativeComparisonFailure};
        use mettail_runtime::binding_receipt::BindingCharge;
        #scaled_helper
        #(#functions)*
        fn main() {
            let left = Binder(FreeVar::fresh_named("left".to_owned()));
            let right = Binder(FreeVar::fresh_named("right".to_owned()));
            check_single(&left, &right, 71);
            check_single(&left, &left, 71);
            check_multi(&vec![], &vec![], 27);
            check_multi(&vec![left.clone()], &vec![right.clone()], 107);
            check_multi(&vec![left.clone()], &vec![right.clone(), right.clone()], 5);
            check_multi(&vec![left.clone(); 1000], &vec![right; 1000], 80027);
            println!("generated single/multi pattern metadata passes every reservation cut");
        }
    };
    syn::parse2::<syn::File>(fixture.clone()).expect("pattern fixture syntax");
    if std::env::var_os("METTAIL_CAPTURE_CHECKED_CMP").is_some() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/verification/cmp-emitter");
        std::fs::create_dir_all(&directory).expect("create comparison fixture directory");
        std::fs::write(directory.join("pattern-contributions.rs"), fixture.to_string())
            .expect("capture actual pattern-control fragments");
    }
}
