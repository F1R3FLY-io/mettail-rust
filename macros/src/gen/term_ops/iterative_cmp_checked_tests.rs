//! Checked comparison over the existing production-layout Hash fixture.
use super::*;
use crate::gen::term_ops::iterative_hash::checked_tests::{fixture_language, literal_label};

fn compact(tokens: TokenStream) -> String {
    tokens.to_string().split_whitespace().collect()
}

fn ordered(source: &str, needles: &[&str]) {
    let mut rest = source;
    for needle in needles {
        let index = rest
            .find(needle)
            .unwrap_or_else(|| panic!("missing {needle} in {source}"));
        rest = &rest[index + needle.len()..];
    }
}

#[test]
fn checked_companion_has_no_tls_and_checks_support_before_alias_or_indices() {
    let language = fixture_language();
    let generated = generate_checked_iterative_cmp(&language);
    let items = syn::parse2::<syn::File>(generated.clone()).expect("checked companion syntax");
    let tokens = compact(generated);
    assert!(!tokens.contains("thread_local!"));
    assert!(!tokens.contains(".try_with("));
    assert!(!tokens.contains("std::cell::Cell"));
    for (name, suffix) in [
        ("checked_eq_handle_proc", "std::ptr::eq(left_ptr,right_ptr)"),
        ("checked_cmp_handle_proc", "letl_idx=variant_index_proc(left)"),
    ] {
        let body = items
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(item) if item.sig.ident == name => Some(&item.block),
                _ => None,
            })
            .expect("checked category helper");
        let body = compact(quote! { #body });
        ordered(
            &body,
            &[
                "checked_cmp_handle_proc_support(unsafe{&*left_ptr})",
                "checked_cmp_handle_proc_support(unsafe{&*right_ptr})",
                suffix,
            ],
        );
        if name == "checked_eq_handle_proc" {
            ordered(&body, &["std::ptr::eq(left_ptr,right_ptr)", "variant_index_proc(left)"]);
        }
    }
}

#[test]
fn checked_comparison_captures_actual_production_layout_executable() {
    let language = fixture_language();
    let declarations =
        syn::parse2::<syn::File>(crate::gen::types::enums::generate_ast_enums(&language))
            .expect("production enum declarations");
    let enum_types: Vec<_> = declarations
        .items
        .into_iter()
        .filter_map(|item| match item {
            syn::Item::Enum(mut item) if language.types.iter().any(|ty| ty.name == item.ident) => {
                item.attrs.clear();
                Some(item)
            },
            _ => None,
        })
        .collect();
    assert_eq!(enum_types.len(), language.types.len());
    let ordinary_clone = crate::gen::term_ops::iterative_clone::generate_iterative_clone(&language);
    let ordinary_cmp = generate_iterative_cmp(&language);
    let ordinary_hash = crate::gen::term_ops::iterative_hash::generate_iterative_hash(&language);
    let ordinary_drop = crate::gen::term_ops::iterative_drop::generate_iterative_drop(&language);
    let checked = generate_checked_iterative_cmp(&language);
    let proc_var = crate::gen::generate_var_label(&format_ident!("Proc"));
    let int_literal = literal_label(&language, "Int");
    let bool_literal = literal_label(&language, "Bool");
    let text_literal = literal_label(&language, "Text");
    let list_literal = literal_label(&language, "List");
    let bag_literal = literal_label(&language, "Bag");
    let map_literal = literal_label(&language, "Map");
    let set_literal = literal_label(&language, "Set");
    let pathmap_literal = literal_label(&language, "Pathmap");
    let bytes_literal = literal_label(&language, "Bytes");
    let fixture = quote! {
        #![allow(dead_code, unused_variables, unreachable_patterns, non_snake_case)]
        use std::cmp::Ordering;
        use std::hash::{Hash, Hasher};
        use std::sync::Arc;
        use mettail_runtime::{Binder, BindingFailure, CheckedIterativeComparison,
            FltNode, FltTemplateBounds, FreeVar, NativeComparisonFailure, OrdVar, Scope, Var};
        #(#enum_types)*
        #ordinary_clone #ordinary_cmp #ordinary_hash #ordinary_drop #checked

        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        enum Answer { Equality(bool), Ordering(Ordering) }

        fn native<T: Ord>(left: &T, right: &T, ordering: bool) -> Answer {
            if ordering { Answer::Ordering(left.cmp(right)) }
            else { Answer::Equality(left == right) }
        }

        fn run<T: CheckedIterativeComparison, E>(left: &T, right: &T, ordering: bool,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<Answer, NativeComparisonFailure<E>> {
            if ordering { left.try_cmp_iterative(right, reserve).map(Answer::Ordering) }
            else { left.try_eq_iterative(right, reserve).map(Answer::Equality) }
        }

        fn exercise<T: CheckedIterativeComparison>(left: &T, right: &T) {
            for ordering in [false, true] {
                let expected = native(left, right, ordering);
                let mut trace = Vec::new();
                assert_eq!(run(left, right, ordering, &mut |w,u| {
                    trace.push((w,u)); Ok::<_, usize>(())
                }), Ok(expected));
                let total = trace.iter().fold((0usize,0usize), |(w,u),(x,y)| (
                    w.checked_add(*x).expect("fixture work fits"),
                    u.checked_add(*y).expect("fixture units fit"),
                ));
                assert!(total.0 > 0 && total.1 > 0);
                for stop in 1..=trace.len() {
                    let mut observed = Vec::new();
                    let result = run(left, right, ordering, &mut |w,u| {
                        observed.push((w,u));
                        if observed.len() == stop { Err(stop) } else { Ok(()) }
                    });
                    assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                        BindingFailure::Reservation(n))) if n == stop));
                    assert_eq!(observed, trace[..stop]);
                }
                for limit in [(total.0-1,total.1), (total.0,total.1-1), total] {
                    let mut used = (0usize,0usize);
                    let result = run(left, right, ordering, &mut |w,u| {
                        if w > limit.0-used.0 || u > limit.1-used.1 { return Err(0usize); }
                        used.0 += w; used.1 += u; Ok(())
                    });
                    if limit == total { assert_eq!(result, Ok(expected)); assert_eq!(used, total); }
                    else { assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                        BindingFailure::Reservation(0))))); }
                }
                assert_eq!(native(left, right, ordering), expected, "borrowed source preserved");
            }
        }

        fn refuse<T: CheckedIterativeComparison>(left: &T, right: &T,
            category: &str, constructor: &str, root_callbacks: Option<usize>,
        ) {
            for ordering in [false, true] {
                let mut trace = Vec::new();
                let result = run(left, right, ordering, &mut |w,u| {
                    trace.push((w,u)); Ok::<_, ()>(())
                });
                assert!(matches!(result, Err(NativeComparisonFailure::UnsupportedConstructor {
                    category: c, constructor: k,
                }) if c == category && k == constructor));
                if let Some(count) = root_callbacks {
                    // Root header, root push, pop, dispatch, then paid operand
                    // support probes. No alias or discriminant charge is reached.
                    assert_eq!(trace.len(), count);
                    assert_eq!(&trace[..2], &[(2,4),(2,4)]);
                    assert!(trace[2..].iter().all(|entry| *entry == (1,0)));
                }
            }
        }

        fn guest(selector: FreeVar<String>) -> Arc<FltNode> {
            Arc::new(FltNode {
                selector: OrdVar(Var::Free(selector)), selector_name: "guest".into(),
                category: "Proc".into(), open_src: "`".into(), body_src: "λ".into(),
                holes: Vec::new(), pieces: vec![mettail_runtime::FltTemplatePiece::Text {
                    text: "λ".into(), range: mettail_runtime::FltSourceRange::new(0,2),
                }], close_src: "`".into(), bounds: FltTemplateBounds::default(), position: 7,
            })
        }

        fn terminal_drain_refusal_is_not_a_completed_ordering() {
            let left = Proc::PPair(Arc::new(Proc::PToken("a".into())),
                Arc::new(Proc::PToken("unvisited tail".into())));
            let right = Proc::PPair(Arc::new(Proc::PToken("b".into())),
                Arc::new(Proc::PToken("unvisited tail".into())));
            let mut trace = Vec::new();
            assert_eq!(left.try_cmp_iterative(&right, &mut |w,u| {
                trace.push((w,u)); Ok::<_, usize>(())
            }), Ok(Ordering::Less));
            // First-child mismatch leaves one child pending: begin, its
            // pop/discard route, then the terminal empty pop.
            assert_eq!(&trace[trace.len()-4..], &[(1,0);4]);
            let mut seen = 0;
            let result = left.try_cmp_iterative(&right, &mut |_,_| {
                seen += 1; if seen == trace.len() { Err("terminal") } else { Ok(()) }
            });
            assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                BindingFailure::Reservation("terminal")))));
            assert_eq!(seen, trace.len());
            exercise(&left, &right);
        }

        fn deep(bottom: &str) -> Proc {
            let mut value = Proc::PToken(bottom.into());
            for depth in 0..20_000 {
                value = if depth % 2 == 0 { Proc::PVector(vec![value]) }
                else { Proc::PMulti(Vec::new(), Scope::from_parts_unsafe(Vec::new(), Arc::new(value))) };
            }
            value
        }

        fn deep_small_stack() {
            std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
                // Independent trees prevent Arc aliasing from hiding traversal.
                let left = deep("a"); let equal = deep("a"); let different = deep("b");
                for right in [&equal, &different] {
                    for ordering in [false, true] {
                        let expected = native(&left, right, ordering);
                        let mut calls = 0usize; let mut total = (0usize,0usize);
                        assert_eq!(run(&left, right, ordering, &mut |w,u| {
                            calls += 1;
                            total.0 = total.0.checked_add(w).expect("deep work fits");
                            total.1 = total.1.checked_add(u).expect("deep units fit");
                            Ok::<_, usize>(())
                        }), Ok(expected));
                        assert!(calls > 20_000);
                        for stop in [1, calls/2, calls] {
                            let mut seen = 0usize;
                            let result = run(&left, right, ordering, &mut |_,_| {
                                seen += 1; if seen == stop { Err(stop) } else { Ok(()) }
                            });
                            assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                                BindingFailure::Reservation(n))) if n == stop));
                            assert_eq!(seen, stop);
                        }
                        for limit in [(total.0-1,total.1), (total.0,total.1-1), total] {
                            let mut used = (0usize,0usize);
                            let result = run(&left, right, ordering, &mut |w,u| {
                                if w > limit.0-used.0 || u > limit.1-used.1 { return Err(0usize); }
                                used.0 += w; used.1 += u; Ok(())
                            });
                            if limit == total { assert_eq!(result, Ok(expected)); assert_eq!(used, total); }
                            else { assert!(matches!(result, Err(NativeComparisonFailure::Admission(
                                BindingFailure::Reservation(0))))); }
                        }
                    }
                }
                drop((left, equal, different));
            }).expect("spawn checked comparison worker").join().expect("20k small-stack comparison");
        }

        fn main() {
            assert!(mettail_runtime::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE);
            exercise(&Proc::PZero, &Proc::PZero);
            exercise(&Proc::PZero, &Proc::PToken("different constructor".into()));
            for (left,right) in [(i64::MIN,i64::MAX), (0,0), (7,-7)] {
                exercise(&Int::#int_literal(left), &Int::#int_literal(right));
            }
            for left in [false,true] { for right in [false,true] {
                exercise(&Bool::#bool_literal(left), &Bool::#bool_literal(right));
            }}
            for (left,right) in [("",""), ("a","ab"), ("ab","ac"), ("λ","μ")] {
                exercise(&Text::#text_literal(left.into()), &Text::#text_literal(right.into()));
            }
            let free = FreeVar::fresh_named("diagnostic identity hint");
            let variable = Proc::#proc_var(OrdVar(Var::Free(free.clone())));
            exercise(&variable, &variable.clone());
            exercise(&variable, &Proc::#proc_var(OrdVar(Var::Free(FreeVar::fresh_named("other")))));
            let bound = Proc::#proc_var(OrdVar(Var::Bound(mettail_runtime::BoundVar {
                scope: moniker::ScopeOffset(3), binder: moniker::BinderIndex(2),
                pretty_name: Some("ignored".into()),
            })));
            exercise(&variable, &bound); exercise(&bound, &bound.clone());
            let child = Arc::new(Proc::PToken("child".into()));
            let guest = guest(free.clone());
            let values = vec![
                Proc::PScalars(Arc::new(Int::#int_literal(-7)), Arc::new(Bool::#bool_literal(true)),
                    Arc::new(Text::#text_literal("text".into()))),
                Proc::PPair(child.clone(), child.clone()),
                Proc::PGuest(guest.clone()),
                Proc::PMixed("prefix".into(), child.clone(), guest.clone(), "suffix".into()),
                Proc::POptionalVec(None), Proc::POptionalVec(Some(Vec::new())),
                Proc::POptionalVec(Some(vec![Proc::PZero, Proc::PToken("last".into())])),
                Proc::PSingle(Arc::new(Proc::PZero),
                    Scope::from_parts_unsafe(Binder(free.clone()), child.clone())),
                Proc::PMulti(vec![Proc::PZero],
                    Scope::from_parts_unsafe(vec![Binder(free.clone())], child.clone())),
            ];
            for value in &values { exercise(value, value); exercise(value, &value.clone()); }
            exercise(&Proc::POptionalVec(None), &Proc::POptionalVec(Some(Vec::new())));
            exercise(&Proc::POptionalVec(Some(vec![Proc::PZero])),
                &Proc::POptionalVec(Some(vec![Proc::PToken("different".into())])));
            exercise(&Proc::PMixed("prefix".into(), Arc::new(Proc::PToken("a".into())),
                    guest.clone(), "z".into()),
                &Proc::PMixed("prefix".into(), Arc::new(Proc::PToken("b".into())),
                    guest.clone(), "a".into()));
            exercise(&Proc::PSingle(Arc::new(Proc::PZero),
                    Scope::from_parts_unsafe(Binder(free.clone()), child.clone())),
                &Proc::PSingle(Arc::new(Proc::PZero),
                    Scope::from_parts_unsafe(Binder(FreeVar::fresh_named("other")), child.clone())));
            exercise(&Proc::PMulti(Vec::new(), Scope::from_parts_unsafe(Vec::new(), child.clone())),
                &Proc::PMulti(Vec::new(), Scope::from_parts_unsafe(vec![Binder(free)], child.clone())));
            for width in [0,1,3] {
                let left = Proc::PVector((0..width).map(|i| Proc::PToken(i.to_string())).collect());
                exercise(&left, &left.clone());
                exercise(&left, &Proc::PVector(Vec::new()));
            }
            exercise(&List::#list_literal(vec![Proc::PZero, Proc::PToken("a".into())]),
                &List::#list_literal(vec![Proc::PZero, Proc::PToken("b".into())]));

            let predicate = Proc::PPredicate(mettail_runtime::BehavioralPred::RelationQuery {
                relation_name: "unadmitted".into(), args: Vec::new(), negated: false,
            });
            refuse(&predicate, &predicate, "Proc", "PPredicate", Some(5));
            refuse(&predicate, &Proc::PZero, "Proc", "PPredicate", Some(5));
            refuse(&Proc::PZero, &predicate, "Proc", "PPredicate", Some(6));
            let predicate = Arc::new(predicate);
            refuse(&Proc::PUnary(predicate.clone()), &Proc::PUnary(predicate),
                "Proc", "PPredicate", None);
            let optional = Proc::POptional("prefix".into(), None, None, None);
            refuse(&optional, &optional, "Proc", "POptional", Some(5));
            let bag = Proc::PBag(mettail_runtime::HashBag::new());
            refuse(&bag, &bag, "Proc", "PBag", Some(5));
            let bag = Bag::#bag_literal(mettail_runtime::HashBag::new());
            refuse(&bag, &bag, "Bag", stringify!(#bag_literal), Some(5));
            let map = Map::#map_literal(mettail_runtime::HashMapLit::new());
            refuse(&map, &map, "Map", stringify!(#map_literal), Some(5));
            let set = Set::#set_literal(mettail_runtime::HashSetLit::new());
            refuse(&set, &set, "Set", stringify!(#set_literal), Some(5));
            let pathmap = Pathmap::#pathmap_literal(mettail_runtime::PathMapLit::new());
            refuse(&pathmap, &pathmap, "Pathmap", stringify!(#pathmap_literal), Some(5));
            let bytes = Bytes::#bytes_literal(vec![0,1,255]);
            refuse(&bytes, &bytes, "Bytes", stringify!(#bytes_literal), Some(5));
            terminal_drain_refusal_is_not_a_completed_ordering();
            deep_small_stack();
            println!("checked generated Eq/Ord native parity, all small cutpoints, exact limits, local unsupported gates and 20k small-stack traversal verified");
        }
    };
    syn::parse2::<syn::File>(fixture.clone()).expect("actual checked comparison fixture syntax");
    if std::env::var_os("METTAIL_CAPTURE_CHECKED_CMP").is_some() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/verification/cmp-emitter");
        std::fs::create_dir_all(&directory).expect("create checked comparison fixture directory");
        std::fs::write(directory.join("checked.rs"), fixture.to_string())
            .expect("capture actual checked comparison fixture");
    }
}
