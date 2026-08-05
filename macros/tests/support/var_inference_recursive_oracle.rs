use super::*;
use proc_macro2::{Ident, Span};

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn recursive_extract_base_cat(ty: &TypeExpr) -> Ident {
    match ty {
        TypeExpr::Base(ident) => ident.clone(),
        TypeExpr::Collection { element, .. } => recursive_extract_base_cat(element),
        TypeExpr::Arrow { codomain, .. } => recursive_extract_base_cat(codomain),
        TypeExpr::MultiBinder(inner) => recursive_extract_base_cat(inner),
        TypeExpr::Refined { base, .. } => recursive_extract_base_cat(base),
        TypeExpr::Map { value, .. } => recursive_extract_base_cat(value),
    }
}

fn recursive_collect(
    params: &[TermParam],
    all_cats: &[&Ident],
    flat_idx: &mut usize,
    wrap: InferFieldWrap,
    out: &mut Vec<(Ident, Ident, InferFieldKind, InferFieldWrap)>,
) {
    for param in params {
        match param {
            TermParam::Simple { ty, .. } => {
                let index = *flat_idx;
                *flat_idx += 1;
                let category = recursive_extract_base_cat(ty);
                if all_cats
                    .iter()
                    .any(|candidate| candidate.to_string() == category.to_string())
                {
                    let kind = match ty {
                        TypeExpr::Collection { coll_type, .. } => {
                            InferFieldKind::Collection(coll_type.clone())
                        },
                        TypeExpr::Map { .. } => InferFieldKind::Collection(CollectionType::HashMap),
                        _ => InferFieldKind::Simple,
                    };
                    out.push((ident(&format!("f{index}")), category, kind, wrap));
                }
            },
            TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => {
                let index = *flat_idx;
                *flat_idx += 1;
                let category = recursive_extract_base_cat(ty);
                if all_cats
                    .iter()
                    .any(|candidate| candidate.to_string() == category.to_string())
                {
                    let kind = if matches!(param, TermParam::Abstraction { .. }) {
                        InferFieldKind::Binder
                    } else {
                        InferFieldKind::MultiBinder
                    };
                    out.push((ident(&format!("f{index}")), category, kind, wrap));
                }
            },
            TermParam::GuardBody { .. } => *flat_idx += 1,
            TermParam::Optional { params: inner } => {
                recursive_collect(inner, all_cats, flat_idx, InferFieldWrap::Optional, out);
            },
        }
    }
}

fn recursive_flat_count(params: &[TermParam]) -> usize {
    params
        .iter()
        .map(|param| match param {
            TermParam::Optional { params: inner } => recursive_flat_count(inner),
            _ => 1,
        })
        .sum()
}

fn recursive_contains_guard(params: &[TermParam]) -> bool {
    params.iter().any(|param| match param {
        TermParam::GuardBody { .. } => true,
        TermParam::Optional { params: inner } => recursive_contains_guard(inner),
        _ => false,
    })
}

fn shallow_fixture(depth: usize) -> Vec<TermParam> {
    let mut nested = TermParam::Simple {
        name: ident("entry"),
        ty: TypeExpr::Collection {
            coll_type: CollectionType::PathMap,
            element: Box::new(TypeExpr::Base(ident("Proc"))),
        },
    };
    for _ in 0..depth {
        nested = TermParam::Optional { params: vec![nested] };
    }
    vec![
        nested,
        TermParam::Abstraction {
            binder: ident("x"),
            body: ident("body"),
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::Base(ident("Name"))),
                codomain: Box::new(TypeExpr::Base(ident("Proc"))),
            },
        },
        TermParam::MultiAbstraction {
            binder: ident("xs"),
            body: ident("body"),
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::MultiBinder(Box::new(TypeExpr::Base(ident("Name"))))),
                codomain: Box::new(TypeExpr::Base(ident("Proc"))),
            },
        },
        TermParam::GuardBody { name: ident("guard") },
    ]
}

#[test]
fn iterative_inference_walkers_match_recursive_oracles() {
    let proc = ident("Proc");
    let name = ident("Name");
    let all_cats = [&proc, &name];
    for depth in 0..64 {
        let params = shallow_fixture(depth);
        let mut actual_index = 0;
        let mut expected_index = 0;
        let mut actual = Vec::new();
        let mut expected = Vec::new();
        collect_inference_fields(
            &params,
            &all_cats,
            &mut actual_index,
            InferFieldWrap::Direct,
            &mut actual,
        );
        recursive_collect(
            &params,
            &all_cats,
            &mut expected_index,
            InferFieldWrap::Direct,
            &mut expected,
        );
        assert_eq!(actual_index, expected_index);
        assert_eq!(actual, expected);
        assert_eq!(flat_term_param_count(&params), recursive_flat_count(&params));
        assert_eq!(contains_guard_param(&params), recursive_contains_guard(&params));
    }

    let ty = TypeExpr::Map {
        key: Box::new(TypeExpr::Base(ident("Name"))),
        value: Box::new(TypeExpr::Refined {
            var: ident("p"),
            base: Box::new(TypeExpr::Collection {
                coll_type: CollectionType::PathMap,
                element: Box::new(TypeExpr::Base(ident("Proc"))),
            }),
            predicate_repr: "safe(p)".into(),
        }),
    };
    assert_eq!(extract_base_cat(&ty).to_string(), recursive_extract_base_cat(&ty).to_string());
}

#[test]
fn deep_inference_metadata_walks_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("var-inference-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut param = TermParam::Simple {
                name: ident("entry"),
                ty: TypeExpr::Base(ident("Proc")),
            };
            for _ in 0..DEPTH {
                param = TermParam::Optional { params: vec![param] };
            }
            let params = vec![param];
            let proc = ident("Proc");
            let all_cats = [&proc];
            let mut flat_index = 0;
            let mut fields = Vec::new();
            collect_inference_fields(
                &params,
                &all_cats,
                &mut flat_index,
                InferFieldWrap::Direct,
                &mut fields,
            );
            assert_eq!(flat_index, 1);
            assert_eq!(fields.len(), 1);
            assert_eq!(flat_term_param_count(&params), 1);
            assert!(!contains_guard_param(&params));
            drop(params);

            let mut ty = TypeExpr::Base(ident("Proc"));
            for _ in 0..DEPTH {
                ty = TypeExpr::MultiBinder(Box::new(ty));
            }
            assert_eq!(extract_base_cat(&ty), "Proc");
            drop(ty);
        })
        .expect("small-stack inference walker thread must spawn");
    handle
        .join()
        .expect("inference metadata PDAs must not overflow the native stack");
}
