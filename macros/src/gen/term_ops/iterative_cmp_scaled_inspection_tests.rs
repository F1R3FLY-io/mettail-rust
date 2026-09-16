use super::*;

#[test]
fn capture_checked_scaling_and_accumulation_for_execution() {
    let helper = CmpEmissionNames::inspect_scaled_accumulation_helper();
    syn::parse2::<syn::ItemFn>(helper.clone()).expect("private scaling helper syntax");
    let fixture = quote! {
        use mettail_runtime::binding_receipt::BindingCharge;
        use mettail_runtime::{BindingFailure, NativeComparisonFailure};
        #helper

        fn check_success(parts: (usize, usize, usize), factor: usize) {
            let (work, records, bytes) = parts;
            let initial = BindingCharge::new(7, 2, 3).expect("initial charge");
            for limit in 0usize..=2 {
                let mut state = initial;
                let mut trace = Vec::new();
                let result = inspect_cmp_scaled_contribution(
                    &mut state, work, records, bytes, factor, &mut |w, u| {
                        trace.push((w, u));
                        if trace.len() > limit { Err(limit) } else { Ok(()) }
                    },
                );
                if limit < 2 {
                    assert_eq!(result, Err(NativeComparisonFailure::Admission(
                        BindingFailure::Reservation(limit))));
                    assert_eq!(state, initial);
                    assert_eq!(trace, vec![(1, 0); limit + 1]);
                } else {
                    assert_eq!(result, Ok(()));
                    assert_eq!(state.base_work(), 7 + work * factor);
                    assert_eq!(state.records(), 2 + records * factor);
                    assert_eq!(state.owned_bytes(), 3 + bytes * factor);
                    assert_eq!(trace, [(1, 0); 2]);
                }
            }
        }

        fn check_overflow(
            initial: BindingCharge, parts: (usize, usize, usize), factor: usize,
            groups: usize,
        ) {
            let mut state = initial;
            let mut trace = Vec::new();
            let result = inspect_cmp_scaled_contribution(
                &mut state, parts.0, parts.1, parts.2, factor, &mut |w, u| {
                    trace.push((w, u)); Ok::<_, ()>(())
                },
            );
            assert_eq!(result, Err(NativeComparisonFailure::Admission(
                BindingFailure::SizeOverflow)));
            assert_eq!(state, initial);
            assert_eq!(trace, vec![(1, 0); groups]);
        }

        fn check_original_error_moves_without_cloning() {
            struct Stop(Box<u8>);
            for limit in 0usize..2 {
                let initial = BindingCharge::new(7, 2, 3).expect("initial charge");
                let mut state = initial;
                let mut error = Some(Stop(Box::new(42)));
                let identity: *const u8 = &*error.as_ref().expect("original error").0;
                let mut calls = 0;
                let result = inspect_cmp_scaled_contribution(
                    &mut state, 3, 2, 1, 4, &mut |w, u| {
                        assert_eq!((w, u), (1, 0));
                        calls += 1;
                        if calls > limit { Err(error.take().expect("one refusal")) }
                        else { Ok(()) }
                    },
                );
                match result {
                    Err(NativeComparisonFailure::Admission(BindingFailure::Reservation(e))) =>
                        assert_eq!(&*e.0 as *const u8, identity),
                    _ => panic!("must preserve original admission error"),
                }
                assert_eq!(state, initial);
                assert_eq!(calls, limit + 1);
            }
            // Reservation failure precedes even invalid arithmetic.
            let mut state = BindingCharge::ZERO;
            let result = inspect_cmp_scaled_contribution(
                &mut state, usize::MAX, usize::MAX, usize::MAX, 0,
                &mut |_, _| Err::<(), _>(17u8),
            );
            assert_eq!(result, Err(NativeComparisonFailure::Admission(
                BindingFailure::Reservation(17))));
            assert_eq!(state, BindingCharge::ZERO);
        }

        fn main() {
            for factor in [0, 1, 3] { check_success((5, 2, 7), factor); }
            check_success((0, 0, 0), usize::MAX);
            let max = usize::MAX;
            // Raw parts are checked BEFORE scaling, even at factor zero.
            for parts in [(max, 0, 1), (0, max, 0), (0, 1, max)] {
                check_overflow(BindingCharge::ZERO, parts, 0, 1);
            }
            // Component multiplication and final work/retention projections.
            for (parts, factor) in [
                ((max, 0, 0), 2), ((0, 0, max), 2),
                ((0, 1, 0), max), ((0, max / 4, 0), 2),
                ((max / 2, 0, 1), 2), ((0, 1, max / 2), 2),
            ] { check_overflow(BindingCharge::ZERO, parts, factor, 1); }
            // Individually valid scaled parts may still overflow their sum.
            check_overflow(BindingCharge::new(max, 0, 0).expect("max work"), (1, 0, 0), 1, 2);
            check_overflow(BindingCharge::new(0, max / 4, 0).expect("max records"), (0, 1, 0), 1, 2);
            check_overflow(BindingCharge::new(0, 0, max).expect("max bytes"), (0, 0, 1), 1, 2);
            // Exact representability boundary succeeds without enumerating factor copies.
            let mut state = BindingCharge::ZERO;
            let mut trace = Vec::new();
            inspect_cmp_scaled_contribution(&mut state, 1, 0, 0, max, &mut |w, u| {
                trace.push((w, u)); Ok::<_, ()>(())
            }).expect("exact maximum work fits");
            assert_eq!(state.base_work(), max);
            assert_eq!(trace, [(1, 0); 2]);
            check_original_error_moves_without_cloning();
            println!("checked scaling and accumulation preserve arithmetic and admission boundaries");
        }
    };
    syn::parse2::<syn::File>(fixture.clone()).expect("scaled inspection fixture syntax");
    if std::env::var_os("METTAIL_CAPTURE_CHECKED_CMP").is_some() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/verification/cmp-emitter");
        std::fs::create_dir_all(&directory).expect("create comparison fixture directory");
        std::fs::write(directory.join("scaled-contributions.rs"), fixture.to_string())
            .expect("capture actual checked scaling helper");
    }
}
