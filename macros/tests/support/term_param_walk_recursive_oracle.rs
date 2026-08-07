use super::*;
use mettail_ast::types::TypeExpr;
use proc_macro2::Span;
use syn::Ident;

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn collect_recursive<'a>(
    params: &'a [TermParam],
    is_optional: bool,
    out: &mut Vec<TermParamLeaf<'a>>,
) {
    for param in params {
        match param {
            TermParam::Optional { params } => collect_recursive(params, true, out),
            TermParam::Simple { name, ty } => out.push(TermParamLeaf {
                kind: TermParamLeafKind::Simple { param, name, ty },
                is_optional,
            }),
            TermParam::GuardBody { name } => out.push(TermParamLeaf {
                kind: TermParamLeafKind::GuardBody { param, name },
                is_optional,
            }),
            TermParam::Abstraction { binder, body, ty } => out.push(TermParamLeaf {
                kind: TermParamLeafKind::Abstraction { param, binder, body, ty },
                is_optional,
            }),
            TermParam::MultiAbstraction { binder, body, ty } => out.push(TermParamLeaf {
                kind: TermParamLeafKind::MultiAbstraction { param, binder, body, ty },
                is_optional,
            }),
        }
    }
}

#[test]
fn leaf_iterator_matches_recursive_preorder_on_every_term_param_variant() {
    let params = vec![
        TermParam::Simple {
            name: ident("head"),
            ty: TypeExpr::Base(ident("Proc")),
        },
        TermParam::Optional {
            params: vec![
                TermParam::GuardBody { name: ident("guard") },
                TermParam::Abstraction {
                    binder: ident("x"),
                    body: ident("body"),
                    ty: TypeExpr::Base(ident("Proc")),
                },
                TermParam::Optional {
                    params: vec![TermParam::MultiAbstraction {
                        binder: ident("xs"),
                        body: ident("multi_body"),
                        ty: TypeExpr::Base(ident("Proc")),
                    }],
                },
            ],
        },
    ];

    let actual: Vec<_> = TermParamLeaves::new(&params, false).collect();
    let mut expected = Vec::new();
    collect_recursive(&params, false, &mut expected);
    assert_eq!(actual.len(), expected.len());
    for (actual, expected) in actual.iter().zip(expected) {
        assert!(std::ptr::eq(actual.kind.param(), expected.kind.param()));
        assert_eq!(actual.is_optional, expected.is_optional);
    }
}

#[test]
fn leaf_iterator_handles_20k_nesting_on_a_256k_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut nested = TermParam::Simple {
                name: ident("leaf"),
                ty: TypeExpr::Base(ident("Proc")),
            };
            for _ in 0..20_000 {
                nested = TermParam::Optional { params: vec![nested] };
            }
            let params = [nested];
            let leaves: Vec<_> = TermParamLeaves::new(&params, false).collect();
            assert_eq!(leaves.len(), 1);
            assert!(leaves[0].is_optional);
        })
        .expect("spawn low-stack term-parameter iterator gate")
        .join()
        .expect("term-parameter iterator must not consume nesting-proportional call stack");
}
