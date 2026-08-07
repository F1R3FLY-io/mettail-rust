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
