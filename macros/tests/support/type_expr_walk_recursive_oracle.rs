use super::*;
use mettail_ast::types::CollectionType;
use proc_macro2::Span;
use syn::Ident;

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn terminal_base_recursive(ty: &TypeExpr) -> &Ident {
    match ty {
        TypeExpr::Base(ident) => ident,
        TypeExpr::Collection { element, .. } => terminal_base_recursive(element),
        TypeExpr::Arrow { codomain, .. } => terminal_base_recursive(codomain),
        TypeExpr::MultiBinder(inner) => terminal_base_recursive(inner),
        TypeExpr::Refined { base, .. } => terminal_base_recursive(base),
        TypeExpr::Map { value, .. } => terminal_base_recursive(value),
    }
}

fn collect_base_idents_recursive<'a>(ty: &'a TypeExpr, out: &mut Vec<&'a Ident>) {
    match ty {
        TypeExpr::Base(ident) => out.push(ident),
        TypeExpr::Arrow { domain, codomain } => {
            collect_base_idents_recursive(domain, out);
            collect_base_idents_recursive(codomain, out);
        },
        TypeExpr::MultiBinder(inner) => collect_base_idents_recursive(inner, out),
        TypeExpr::Collection { element, .. } => collect_base_idents_recursive(element, out),
        TypeExpr::Refined { base, .. } => collect_base_idents_recursive(base, out),
        TypeExpr::Map { key, value } => {
            collect_base_idents_recursive(key, out);
            collect_base_idents_recursive(value, out);
        },
    }
}

#[test]
fn base_ident_iterator_matches_recursive_preorder_on_every_type_expr_variant() {
    let ty = TypeExpr::Collection {
        coll_type: CollectionType::HashBag,
        element: Box::new(TypeExpr::Arrow {
            domain: Box::new(TypeExpr::MultiBinder(Box::new(TypeExpr::Base(ident("Domain"))))),
            codomain: Box::new(TypeExpr::Map {
                key: Box::new(TypeExpr::Refined {
                    var: ident("key"),
                    base: Box::new(TypeExpr::Base(ident("Key"))),
                    predicate_repr: "KeyPred(key)".to_string(),
                }),
                value: Box::new(TypeExpr::Base(ident("Value"))),
            }),
        }),
    };
    let actual: Vec<_> = TypeExprBaseIdents::new(&ty).collect();
    let mut expected = Vec::new();
    collect_base_idents_recursive(&ty, &mut expected);
    assert_eq!(actual.len(), expected.len());
    assert!(actual
        .iter()
        .zip(&expected)
        .all(|(left, right)| std::ptr::eq(*left, *right)));
    assert_eq!(
        actual.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
        ["Domain", "Key", "Value"]
    );
}

#[test]
fn terminal_base_matches_recursive_equation_on_every_type_expr_variant() {
    let ty = TypeExpr::Collection {
        coll_type: CollectionType::Vec,
        element: Box::new(TypeExpr::Arrow {
            domain: Box::new(TypeExpr::Base(ident("IgnoredDomain"))),
            codomain: Box::new(TypeExpr::MultiBinder(Box::new(TypeExpr::Refined {
                base: Box::new(TypeExpr::Map {
                    key: Box::new(TypeExpr::Base(ident("IgnoredKey"))),
                    value: Box::new(TypeExpr::Base(ident("Result"))),
                }),
                var: ident("x"),
                predicate_repr: "Pred(x)".to_string(),
            }))),
        }),
    };
    let actual = terminal_base(&ty);
    let expected = terminal_base_recursive(&ty);
    assert!(std::ptr::eq(actual, expected));
    assert_eq!(actual, "Result");
}

#[test]
fn terminal_base_handles_20k_nesting_on_a_256k_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut ty = TypeExpr::Base(ident("Leaf"));
            for _ in 0..20_000 {
                ty = TypeExpr::MultiBinder(Box::new(ty));
            }
            assert_eq!(terminal_base(&ty), "Leaf");
        })
        .expect("spawn low-stack type-expression iterator gate")
        .join()
        .expect("type-expression iterator must not consume nesting-proportional call stack");
}

#[test]
fn base_ident_iterator_handles_20k_nesting_on_a_256k_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut ty = TypeExpr::Base(ident("Leaf"));
            for _ in 0..20_000 {
                ty = TypeExpr::Refined {
                    var: ident("x"),
                    base: Box::new(ty),
                    predicate_repr: "true".to_string(),
                };
            }
            let leaves: Vec<_> = TypeExprBaseIdents::new(&ty).collect();
            assert_eq!(leaves.len(), 1);
            assert_eq!(leaves[0], "Leaf");
        })
        .expect("spawn low-stack base-identifier iterator gate")
        .join()
        .expect("base-identifier iterator must not consume nesting-proportional call stack");
}
