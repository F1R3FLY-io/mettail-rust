use super::*;
use mettail_ast::types::CollectionType;
use proc_macro2::{Ident, Span};

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn recursive_flat_term_param_count(params: &[TermParam]) -> usize {
    params
        .iter()
        .map(|param| match param {
            TermParam::Optional { params: inner } => recursive_flat_term_param_count(inner),
            _ => 1,
        })
        .sum()
}

fn recursive_emit_var_collection_recursion(
    params: &[TermParam],
    field_names: &[Ident],
    field_idx: &mut usize,
    optional_wrap: bool,
    primary_type: &Ident,
    recurse_calls: &mut Vec<TokenStream>,
) {
    for param in params {
        match param {
            TermParam::Simple { ty, .. } => {
                let field_name = &field_names[*field_idx];
                *field_idx += 1;
                let inner_body = match ty {
                    TypeExpr::Base(category)
                        if category.to_string() == primary_type.to_string() =>
                    {
                        Some(quote! {
                            stack.push(CollectTask::Visit(__v.as_ref() as *const _));
                        })
                    },
                    TypeExpr::Collection { coll_type, element } => match element.as_ref() {
                        TypeExpr::Base(category)
                            if category.to_string() == primary_type.to_string() =>
                        {
                            Some(for_each_subterm(
                                coll_type,
                                &quote! { __v },
                                WalkOrder::ReverseForLifo,
                                &|element, _| {
                                    quote! {
                                        stack.push(CollectTask::Visit(#element as *const _));
                                    }
                                },
                            ))
                        },
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(body) = inner_body {
                    if optional_wrap {
                        recurse_calls.push(quote! {
                            if let Some(__v) = #field_name.as_ref() {
                                #body
                            }
                        });
                    } else {
                        recurse_calls.push(quote! {
                            { let __v = #field_name; #body }
                        });
                    }
                }
            },
            TermParam::Abstraction { ty, .. } => {
                let field_name = &field_names[*field_idx];
                *field_idx += 1;
                if let TypeExpr::Arrow { domain, codomain } = ty {
                    if let TypeExpr::Base(category) = codomain.as_ref() {
                        if category.to_string() == primary_type.to_string() {
                            let domain_name = match domain.as_ref() {
                                TypeExpr::Base(domain) => domain.to_string(),
                                _ => "Name".to_owned(),
                            };
                            let domain = LitStr::new(&domain_name, Span::call_site());
                            let body = quote! {
                                stack.push(CollectTask::Binder(__scope as *const _, #domain));
                            };
                            if optional_wrap {
                                recurse_calls.push(quote! {
                                    if let Some(__scope) = #field_name.as_ref() {
                                        #body
                                    }
                                });
                            } else {
                                recurse_calls.push(quote! {
                                    { let __scope = #field_name; #body }
                                });
                            }
                        }
                    }
                }
            },
            TermParam::MultiAbstraction { ty, .. } => {
                let field_name = &field_names[*field_idx];
                *field_idx += 1;
                if let TypeExpr::Arrow { domain, codomain } = ty {
                    if let TypeExpr::Base(category) = codomain.as_ref() {
                        if category.to_string() == primary_type.to_string() {
                            let domain_name = match domain.as_ref() {
                                TypeExpr::MultiBinder(inner) => match inner.as_ref() {
                                    TypeExpr::Base(domain) => domain.to_string(),
                                    _ => "Name".to_owned(),
                                },
                                _ => "Name".to_owned(),
                            };
                            let domain = LitStr::new(&domain_name, Span::call_site());
                            let body = quote! {
                                stack.push(CollectTask::MultiBinder(__scope as *const _, #domain));
                            };
                            if optional_wrap {
                                recurse_calls.push(quote! {
                                    if let Some(__scope) = #field_name.as_ref() {
                                        #body
                                    }
                                });
                            } else {
                                recurse_calls.push(quote! {
                                    { let __scope = #field_name; #body }
                                });
                            }
                        }
                    }
                }
            },
            TermParam::GuardBody { .. } => *field_idx += 1,
            TermParam::Optional { params: inner } => recursive_emit_var_collection_recursion(
                inner,
                field_names,
                field_idx,
                true,
                primary_type,
                recurse_calls,
            ),
        }
    }
}

fn fixture(depth: usize) -> Vec<TermParam> {
    let proc = ident("Proc");
    let name = ident("Name");
    let other = ident("Other");
    let mut nested = TermParam::Simple {
        name: ident("nested"),
        ty: TypeExpr::Collection {
            coll_type: CollectionType::PathMap,
            element: Box::new(TypeExpr::Base(proc.clone())),
        },
    };
    for _ in 0..depth {
        nested = TermParam::Optional { params: vec![nested] };
    }

    vec![
        TermParam::Simple {
            name: ident("direct"),
            ty: TypeExpr::Base(proc.clone()),
        },
        TermParam::Simple {
            name: ident("ignored"),
            ty: TypeExpr::Base(other.clone()),
        },
        nested,
        TermParam::Abstraction {
            binder: ident("x"),
            body: ident("body"),
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::Base(name.clone())),
                codomain: Box::new(TypeExpr::Base(proc.clone())),
            },
        },
        TermParam::Abstraction {
            binder: ident("ignored_binder"),
            body: ident("ignored_body"),
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::Base(name.clone())),
                codomain: Box::new(TypeExpr::Base(other)),
            },
        },
        TermParam::MultiAbstraction {
            binder: ident("xs"),
            body: ident("body"),
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::MultiBinder(Box::new(TypeExpr::Base(name)))),
                codomain: Box::new(TypeExpr::Base(proc)),
            },
        },
        TermParam::GuardBody { name: ident("guard") },
    ]
}

#[test]
fn iterative_language_recursion_emission_matches_recursive_oracle() {
    let primary = ident("Proc");
    for depth in 0..64 {
        let params = fixture(depth);
        let field_count = flat_term_param_count(&params);
        assert_eq!(field_count, recursive_flat_term_param_count(&params));
        let fields: Vec<_> = (0..field_count)
            .map(|index| ident(&format!("f{index}")))
            .collect();

        let mut actual_index = 0;
        let mut expected_index = 0;
        let mut actual = Vec::new();
        let mut expected = Vec::new();
        emit_var_collection_recursion(&params, &fields, &mut actual_index, &primary, &mut actual);
        recursive_emit_var_collection_recursion(
            &params,
            &fields,
            &mut expected_index,
            false,
            &primary,
            &mut expected,
        );

        assert_eq!(actual_index, expected_index);
        assert_eq!(
            actual
                .iter()
                .map(TokenStream::to_string)
                .collect::<Vec<_>>(),
            expected
                .iter()
                .map(TokenStream::to_string)
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn deep_language_recursion_emission_fits_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("language-recursion-emitter-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut param = TermParam::Simple {
                name: ident("value"),
                ty: TypeExpr::Base(ident("Proc")),
            };
            for _ in 0..DEPTH {
                param = TermParam::Optional { params: vec![param] };
            }
            let params = vec![param];
            assert_eq!(flat_term_param_count(&params), 1);

            let fields = [ident("f0")];
            let mut field_index = 0;
            let mut calls = Vec::new();
            emit_var_collection_recursion(
                &params,
                &fields,
                &mut field_index,
                &ident("Proc"),
                &mut calls,
            );
            assert_eq!(field_index, 1);
            assert_eq!(calls.len(), 1);
            drop(params);
        })
        .expect("small-stack language recursion emitter thread must spawn");
    handle
        .join()
        .expect("language recursion emission must not overflow the native stack");
}
