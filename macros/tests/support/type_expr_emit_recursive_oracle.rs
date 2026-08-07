use super::*;
use mettail_ast::types::CollectionType;
use proc_macro2::Span;
use syn::Ident;

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn rust_type_recursive(ty: &TypeExpr) -> TokenStream {
    match ty {
        TypeExpr::Base(ident) => quote! { #ident },
        TypeExpr::Collection { coll_type, element } => {
            let element = rust_type_recursive(element);
            match coll_type {
                CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
                    quote! { mettail_runtime::HashBag<#element> }
                },
                CollectionType::HashSet => quote! { std::collections::HashSet<#element> },
                CollectionType::Vec => quote! { Vec<#element> },
            }
        },
        TypeExpr::Arrow { domain, codomain } => {
            let domain = rust_type_recursive(domain);
            let codomain = rust_type_recursive(codomain);
            quote! { (#domain -> #codomain) }
        },
        TypeExpr::MultiBinder(inner) => {
            let inner = rust_type_recursive(inner);
            quote! { Vec<#inner> }
        },
        TypeExpr::Refined { base, .. } => rust_type_recursive(base),
        TypeExpr::Map { key, value } => {
            let key = rust_type_recursive(key);
            let value = rust_type_recursive(value);
            quote! { mettail_runtime::HashMapLit<#key, #value> }
        },
    }
}

fn field_type_recursive(ty: &TypeExpr) -> TokenStream {
    match ty {
        TypeExpr::Base(ident) => match NonTerminalKind::classify(&ident.to_string()) {
            NonTerminalKind::Var => quote! { mettail_runtime::OrdVar },
            NonTerminalKind::Integer => quote! { i64 },
            NonTerminalKind::Boolean => quote! { bool },
            NonTerminalKind::StringLiteral | NonTerminalKind::Ident => {
                quote! { std::string::String }
            },
            NonTerminalKind::FloatLiteral => quote! { mettail_runtime::CanonicalFloat64 },
            NonTerminalKind::Category => quote! { std::sync::Arc<#ident> },
        },
        TypeExpr::Collection { coll_type, element } => {
            let element = rust_type_recursive(element);
            match coll_type {
                CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
                    quote! { mettail_runtime::HashBag<#element> }
                },
                CollectionType::HashSet => quote! { std::collections::HashSet<#element> },
                CollectionType::Vec => quote! { Vec<#element> },
            }
        },
        TypeExpr::Arrow { .. } => quote! { Box<dyn std::any::Any> },
        TypeExpr::MultiBinder(inner) => {
            let inner = rust_type_recursive(inner);
            quote! { Vec<#inner> }
        },
        TypeExpr::Refined { base, .. } => field_type_recursive(base),
        TypeExpr::Map { key, value } => {
            let key = rust_type_recursive(key);
            let value = rust_type_recursive(value);
            quote! { mettail_runtime::HashMapLit<#key, #value> }
        },
    }
}

fn all_variant_fixture() -> TypeExpr {
    TypeExpr::Arrow {
        domain: Box::new(TypeExpr::Collection {
            coll_type: CollectionType::HashSet,
            element: Box::new(TypeExpr::MultiBinder(Box::new(TypeExpr::Base(ident("Domain"))))),
        }),
        codomain: Box::new(TypeExpr::Map {
            key: Box::new(TypeExpr::Refined {
                var: ident("key"),
                base: Box::new(TypeExpr::Base(ident("Key"))),
                predicate_repr: "KeyPred(key)".to_string(),
            }),
            value: Box::new(TypeExpr::Collection {
                coll_type: CollectionType::PathMap,
                element: Box::new(TypeExpr::Base(ident("Value"))),
            }),
        }),
    }
}

#[test]
fn iterative_type_emitters_match_recursive_equations() {
    let fixture = all_variant_fixture();
    assert_eq!(
        type_expr_to_rust_type(&fixture).to_string(),
        rust_type_recursive(&fixture).to_string()
    );

    let field_fixtures = [
        TypeExpr::Base(ident("Var")),
        TypeExpr::Base(ident("Integer")),
        TypeExpr::Base(ident("Boolean")),
        TypeExpr::Base(ident("StringLiteral")),
        TypeExpr::Base(ident("Ident")),
        TypeExpr::Base(ident("FloatLiteral")),
        TypeExpr::Base(ident("Proc")),
        fixture,
    ];
    for ty in &field_fixtures {
        assert_eq!(
            type_expr_to_field_type(ty, None).to_string(),
            field_type_recursive(ty).to_string(),
            "field type moved for {}",
            rust_type_recursive(ty)
        );
    }
}

#[test]
fn iterative_type_emitters_handle_20k_nesting_on_a_256k_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut rust_ty = TypeExpr::Base(ident("Leaf"));
            for _ in 0..20_000 {
                rust_ty = TypeExpr::MultiBinder(Box::new(rust_ty));
            }
            let emitted = type_expr_to_rust_type(&rust_ty);
            assert!(emitted.to_string().contains("Leaf"));

            let mut field_ty = TypeExpr::Base(ident("Proc"));
            for depth in 0..20_000 {
                field_ty = TypeExpr::Refined {
                    var: ident("x"),
                    base: Box::new(field_ty),
                    predicate_repr: depth.to_string(),
                };
            }
            assert_eq!(
                type_expr_to_field_type(&field_ty, None).to_string(),
                "std :: sync :: Arc < Proc >"
            );
        })
        .expect("spawn low-stack type-emitter gate")
        .join()
        .expect("type emitters must not consume nesting-proportional native stack");
}
