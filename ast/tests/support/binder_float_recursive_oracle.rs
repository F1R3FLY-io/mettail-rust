use super::*;
use syn::Ident;

fn ident(name: &str) -> Ident {
    syn::parse_str(name).expect("test identifier must parse")
}

fn recursive_base_category_name(ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Base(ident) => Some(ident.to_string()),
        TypeExpr::Collection { element, .. } => recursive_base_category_name(element),
        _ => None,
    }
}

fn recursive_restated_fields_from_params(
    params: &[TermParam],
    in_optional: bool,
    out: &mut Vec<RestatedField>,
) {
    for param in params {
        match param {
            TermParam::Simple { ty, .. } => out.push(restated_field_from_type(ty, in_optional)),
            TermParam::GuardBody { .. } => out.push(RestatedField {
                category: "Guard".to_owned(),
                is_collection: false,
                is_optional: in_optional,
            }),
            TermParam::Optional { params: inner } => {
                recursive_restated_fields_from_params(inner, true, out);
            },
            TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. }
                if in_optional =>
            {
                let category = match ty {
                    TypeExpr::Arrow { codomain, .. } => recursive_base_category_name(codomain)
                        .unwrap_or_else(|| "__unknown".to_owned()),
                    _ => "__unknown".to_owned(),
                };
                out.push(RestatedField {
                    category,
                    is_collection: false,
                    is_optional: true,
                });
            },
            TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. } => {},
        }
    }
}

fn nested_optional(depth: usize, leaf: TermParam) -> Vec<TermParam> {
    let mut leaf = leaf;
    for _ in 0..depth {
        leaf = TermParam::Optional { params: vec![leaf] };
    }
    vec![leaf]
}

fn fixture(depth: usize) -> Vec<TermParam> {
    let mut params = nested_optional(
        depth,
        TermParam::Simple {
            name: ident("nested"),
            ty: TypeExpr::Collection {
                coll_type: CollectionType::PathMap,
                element: Box::new(TypeExpr::Base(ident("Proc"))),
            },
        },
    );
    params.extend([
        TermParam::Simple {
            name: ident("direct"),
            ty: TypeExpr::Base(ident("Name")),
        },
        TermParam::GuardBody { name: ident("guard") },
        TermParam::Optional {
            params: vec![TermParam::Abstraction {
                binder: ident("x"),
                body: ident("body"),
                ty: TypeExpr::Arrow {
                    domain: Box::new(TypeExpr::Base(ident("Name"))),
                    codomain: Box::new(TypeExpr::Collection {
                        coll_type: CollectionType::Vec,
                        element: Box::new(TypeExpr::Base(ident("Proc"))),
                    }),
                },
            }],
        },
        TermParam::Abstraction {
            binder: ident("ignored"),
            body: ident("ignored_body"),
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::Base(ident("Name"))),
                codomain: Box::new(TypeExpr::Base(ident("Proc"))),
            },
        },
    ]);
    params
}

#[test]
fn iterative_rho_net_metadata_walkers_match_recursive_oracles() {
    for depth in 0..64 {
        let params = fixture(depth);
        let mut actual = Vec::new();
        let mut expected = Vec::new();
        restated_fields_from_params(&params, false, &mut actual);
        recursive_restated_fields_from_params(&params, false, &mut expected);
        assert_eq!(actual, expected);
    }

    let ty = TypeExpr::Collection {
        coll_type: CollectionType::PathMap,
        element: Box::new(TypeExpr::Collection {
            coll_type: CollectionType::Vec,
            element: Box::new(TypeExpr::Base(ident("Proc"))),
        }),
    };
    assert_eq!(base_category_name(&ty), recursive_base_category_name(&ty));

    let unsupported = TypeExpr::Arrow {
        domain: Box::new(TypeExpr::Base(ident("Name"))),
        codomain: Box::new(TypeExpr::Base(ident("Proc"))),
    };
    assert_eq!(base_category_name(&unsupported), recursive_base_category_name(&unsupported));
}

#[test]
fn deep_rho_net_metadata_walks_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("rho-net-metadata-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let params = nested_optional(
                DEPTH,
                TermParam::Simple {
                    name: ident("value"),
                    ty: TypeExpr::Base(ident("Proc")),
                },
            );
            let mut fields = Vec::new();
            restated_fields_from_params(&params, false, &mut fields);
            assert_eq!(
                fields,
                [RestatedField {
                    category: "Proc".to_owned(),
                    is_collection: false,
                    is_optional: true,
                }]
            );
            drop(params);

            let mut ty = TypeExpr::Base(ident("Proc"));
            for _ in 0..DEPTH {
                ty = TypeExpr::Collection {
                    coll_type: CollectionType::PathMap,
                    element: Box::new(ty),
                };
            }
            assert_eq!(base_category_name(&ty).as_deref(), Some("Proc"));
            drop(ty);
        })
        .expect("small-stack RhoNet metadata thread must spawn");
    handle
        .join()
        .expect("RhoNet metadata PDAs must not overflow the native stack");
}
