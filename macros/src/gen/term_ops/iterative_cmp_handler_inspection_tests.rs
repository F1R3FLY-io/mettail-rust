use super::*;
use crate::gen::term_ops::iterative_hash::checked_tests::fixture_language;

fn compact(tokens: TokenStream) -> String {
    tokens.to_string().split_whitespace().collect()
}

fn fixture_variant(language: &LanguageDef, category: &str, label: &str) -> VariantKind {
    collect_category_variants(&format_ident!("{category}"), language)
        .into_iter()
        .find(|variant| variant.label() == label)
        .expect("existing fixture variant")
}

#[test]
fn original_field_and_scope_routes_have_one_contribution_each() {
    let language = fixture_language();
    let emission = CmpEmissionNames::inspect_contributions();
    let one = compact(emission.inspect_contribution(1, 0));
    for (label, expected) in [("PZero", 0), ("PPair", 2), ("PMixed", 4), ("PSingle", 2)] {
        let variant = fixture_variant(&language, "Proc", label);
        for arm in [
            generate_eq_variant_arm(&format_ident!("Proc"), &variant, &language, &emission),
            generate_cmp_variant_arm(&format_ident!("Proc"), &variant, &language, &emission),
        ] {
            syn::parse2::<syn::Arm>(arm.clone()).expect("shared variant arm syntax");
            assert_eq!(compact(arm).matches(&one).count(), expected, "{label}");
        }
    }
    let category = format_ident!("Int");
    let literal = collect_category_variants(&category, &language)
        .into_iter()
        .find(|variant| matches!(variant, VariantKind::Literal { .. }))
        .expect("existing Int literal");
    for arm in [
        generate_eq_variant_arm(&category, &literal, &language, &emission),
        generate_cmp_variant_arm(&category, &literal, &language, &emission),
    ] {
        assert_eq!(compact(arm).matches(&one).count(), 1);
    }
}

#[test]
fn ordered_vector_has_one_length_and_original_iterator_contributions() {
    let language = fixture_language();
    let emission = CmpEmissionNames::inspect_contributions();
    let one = compact(emission.inspect_contribution(1, 0));
    let two = compact(emission.inspect_contribution(2, 0));
    let variant = fixture_variant(&language, "Proc", "PVector");
    for arm in [
        generate_eq_variant_arm(&format_ident!("Proc"), &variant, &language, &emission),
        generate_cmp_variant_arm(&format_ident!("Proc"), &variant, &language, &emission),
    ] {
        let source = compact(arm);
        assert_eq!(source.matches(&one).count(), 3, "field, setup, next");
        assert_eq!(source.matches(&two).count(), 1, "length must not be doubled");
        let setup = source.find("letmut__cmp_walk=").expect("original iterator");
        let next = source.find("__cmp_walk.next()").expect("original advance");
        assert_eq!(source[..setup].matches(&one).count(), 2);
        assert_eq!(source[setup..next].matches(&one).count(), 1);
    }
}

#[test]
fn ordinary_and_checked_pair_loop_tokens_are_unchanged() {
    let iterator = quote! { left.iter().zip(right.iter()) };
    let body = quote! { consume(__walk_left, __walk_right); };
    let ordinary = CmpEmissionNames::ordinary();
    assert_eq!(
        compact(ordinary.pair_loop(&iterator, &body)),
        compact(quote! {
            for (__walk_left, __walk_right) in #iterator { #body }
        })
    );
    let checked = CmpEmissionNames::checked();
    let setup = checked.routing();
    let advance = checked.routing();
    assert_eq!(
        compact(checked.pair_loop(&iterator, &body)),
        compact(quote! {{
            #setup
            let mut __cmp_walk = #iterator;
            loop {
                #advance
                let Some((__walk_left, __walk_right)) = __cmp_walk.next() else { break };
                #body
            }
        }})
    );
}

#[test]
fn shared_handlers_return_only_local_recipe_completion() {
    let emission = CmpEmissionNames::inspect_contributions();
    let language = fixture_language();
    for handler in [
        generate_eq_category_handler(&format_ident!("Proc"), &language, &emission),
        generate_cmp_category_handler(&format_ident!("Proc"), &language, &emission),
    ] {
        syn::parse2::<syn::ItemFn>(handler.clone()).expect("unit handler syntax");
        let source = compact(handler);
        assert!(source.contains("Result<(),mettail_runtime::NativeComparisonFailure<E>>"));
        assert!(source.contains("returnOk(())"));
        assert!(source.contains("inspect_cmp_schedule_collection("));
        assert!(source.contains("InspectCmpContributionFrame{task:"));
        for forbidden in [
            "returnOk(false)",
            "returnOk(true)",
            "Ordering::",
            "std::ptr::eq",
            "try_native_",
            "CheckedCollectionCmpPda::try_new",
            "Verdict(",
        ] {
            assert!(!source.contains(forbidden), "unexpected {forbidden}: {source}");
        }
    }
}

#[test]
fn unordered_inspection_schedules_original_rosters_not_comparator_execution() {
    let emission = CmpEmissionNames::inspect_contributions();
    for kind in [CollectionType::HashBag, CollectionType::HashMap] {
        let tokens = inspect_unordered_collection_stmts(
            &format_ident!("Proc"),
            &kind,
            &quote! { left },
            &quote! { right },
            &emission,
        );
        syn::parse2::<syn::Block>(tokens.clone()).expect("roster scheduling syntax");
        let source = compact(tokens);
        assert!(source.contains("(left).try_comparison_roster(reserve)?"));
        assert!(source.contains("(right).try_comparison_roster(reserve)?"));
        assert!(source.contains("::CmpProc(left.cast(),right.cast())"));
        assert_eq!(source.contains("Some("), kind == CollectionType::HashMap);
        for forbidden in ["Ordering::", "return", ".cmp(", "try_resume", "StartCollection"] {
            assert!(!source.contains(forbidden), "unexpected {forbidden}: {source}");
        }
    }
}

#[test]
fn inspection_dispatch_has_constant_shape_as_constructor_width_grows() {
    for width in [1, 64, 256] {
        let constructors = (0..width)
            .map(|index| format!("C{index} . child:Proc |- \"c{index}\" child : Proc;"))
            .collect::<String>();
        let language: LanguageDef = syn::parse_str(&format!(
            "name: InspectionWidth, types {{ Proc }}, terms {{ \
             Zero . |- \"zero\" : Proc; {constructors} }}, equations {{}}, rewrites {{}},"
        ))
        .expect("real growing constructor inventory");
        let emission = CmpEmissionNames::inspect_contributions();
        for tokens in [
            generate_eq_category_handler(&format_ident!("Proc"), &language, &emission),
            generate_cmp_category_handler(&format_ident!("Proc"), &language, &emission),
        ] {
            let function = syn::parse2::<syn::ItemFn>(tokens.clone()).expect("category syntax");
            let helpers = function
                .block
                .stmts
                .iter()
                .filter_map(|statement| match statement {
                    syn::Stmt::Item(syn::Item::Fn(helper)) => Some(helper),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(
                helpers.len(),
                width + 2,
                "one helper per constructor and implicit variable"
            );
            let selector = function
                .block
                .stmts
                .iter()
                .find_map(|statement| {
                    let syn::Stmt::Local(local) = statement else {
                        return None;
                    };
                    let syn::Pat::Type(pattern) = &local.pat else {
                        return None;
                    };
                    let syn::Pat::Ident(binding) = pattern.pat.as_ref() else {
                        return None;
                    };
                    if binding.ident != "execute" {
                        return None;
                    }
                    let syn::Expr::Match(selector) = local.init.as_ref()?.expr.as_ref() else {
                        return None;
                    };
                    Some(selector)
                })
                .expect("one typed function-pointer selector");
            assert_eq!(selector.arms.len(), width + 3, "constructor selectors plus old mismatch");
            for arm in &selector.arms[..width + 2] {
                let syn::Expr::Path(path) = arm.body.as_ref() else {
                    panic!("selector cannot perform payload work or invoke a helper")
                };
                let name = &path.path.segments.last().expect("helper path").ident;
                let helper = helpers
                    .iter()
                    .find(|helper| helper.sig.ident == *name)
                    .expect("co-generated selected helper");
                assert!(helper.attrs.iter().any(|attribute| match &attribute.meta {
                    syn::Meta::List(list) =>
                        list.path.is_ident("inline") && list.tokens.to_string() == "never",
                    _ => false,
                }));
            }
            let text = compact(tokens);
            assert_eq!(
                text.matches("execute(stack,left,right,state,mode,factor,reserve)")
                    .count(),
                1
            );
            assert_eq!(
                text.matches("reserve_binding_parts(3,1,0,reserve)").count(),
                1,
                "one unscaled inspection reservation, outside arm receipt accounting"
            );
        }
        for emission in [CmpEmissionNames::ordinary(), CmpEmissionNames::checked()] {
            for tokens in [
                generate_eq_category_handler(&format_ident!("Proc"), &language, &emission),
                generate_cmp_category_handler(&format_ident!("Proc"), &language, &emission),
            ] {
                assert!(
                    !compact(tokens).contains("letexecute:"),
                    "native comparator emission is unchanged"
                );
            }
        }
    }
}

#[test]
fn inspection_selectors_preserve_exact_original_constructor_arms() {
    let partial: LanguageDef = syn::parse_str(
        "name: PartialInspection, types { ![foreign::Opaque] as Proc }, \
         terms { Zero . |- \"zero\" : Proc; }, equations {}, rewrites {},",
    )
    .expect("explicit unsupported native fixture");
    for language in [fixture_language(), partial] {
        let emission = CmpEmissionNames::inspect_contributions();
        for ty in &language.types {
            let cat = &ty.name;
            for equality in [true, false] {
                let (helper_name, tokens) = if equality {
                    (
                        emission.eq_handler(cat),
                        generate_eq_category_handler(cat, &language, &emission),
                    )
                } else {
                    (
                        emission.cmp_handler(cat),
                        generate_cmp_category_handler(cat, &language, &emission),
                    )
                };
                let function = syn::parse2::<syn::ItemFn>(tokens).expect("category helper");
                let selector = function
                    .block
                    .stmts
                    .iter()
                    .find_map(|statement| {
                        let syn::Stmt::Local(local) = statement else {
                            return None;
                        };
                        let syn::Expr::Match(selector) = local.init.as_ref()?.expr.as_ref() else {
                            return None;
                        };
                        Some(selector)
                    })
                    .expect("selector match");
                for variant in collect_category_variants(cat, &language) {
                    let name = format_ident!("{}_{}", helper_name, variant.label());
                    let helper = function
                        .block
                        .stmts
                        .iter()
                        .find_map(|statement| match statement {
                            syn::Stmt::Item(syn::Item::Fn(helper)) if helper.sig.ident == name => {
                                Some(helper)
                            },
                            _ => None,
                        })
                        .expect("matching constructor helper");
                    let selected = selector
                        .arms
                        .iter()
                        .find(|arm| match arm.body.as_ref() {
                            syn::Expr::Path(path) => {
                                path.path.segments.last().expect("path").ident == name
                            },
                            _ => false,
                        })
                        .expect("matching selector arm");
                    let pattern = variant_wildcard_pattern(cat, &variant);
                    let actual_pattern = &selected.pat;
                    assert_eq!(
                        compact(quote! { #actual_pattern }),
                        compact(quote! { (#pattern, #pattern) })
                    );
                    let syn::Stmt::Expr(syn::Expr::Match(body), _) = &helper.block.stmts[0] else {
                        panic!("constructor wrapper must start with the paired payload match")
                    };
                    let original = if equality {
                        generate_eq_variant_arm(cat, &variant, &language, &emission)
                    } else {
                        generate_cmp_variant_arm(cat, &variant, &language, &emission)
                    };
                    let original =
                        syn::parse2::<syn::Arm>(original).expect("original constructor arm");
                    let actual = &body.arms[0];
                    assert_eq!(compact(quote! { #actual }), compact(quote! { #original }));
                }
            }
        }
    }
}
