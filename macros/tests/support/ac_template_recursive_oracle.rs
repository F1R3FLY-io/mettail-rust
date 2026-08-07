use super::*;
use mettail_rholang_codegen::AcReconstructTemplate as T;

fn ac_template_tokens_recursive(template: &T) -> TokenStream {
    match template {
        T::Var(name) => {
            let name = lit(name);
            quote! { ::mettail_rholang_codegen::AcReconstructTemplate::Var(#name.to_string()) }
        },
        T::Node { constructor, children } => {
            let constructor = lit(constructor);
            let children: Vec<_> = children.iter().map(ac_template_tokens_recursive).collect();
            quote! {
                ::mettail_rholang_codegen::AcReconstructTemplate::Node {
                    constructor: #constructor.to_string(),
                    children: ::std::vec![#(#children),*],
                }
            }
        },
        T::Bag { op, elements, rest } => {
            let op = lit(op);
            let elements: Vec<_> = elements.iter().map(ac_template_tokens_recursive).collect();
            let rest = match rest {
                Some(rest) => {
                    let rest = lit(rest);
                    quote! { ::core::option::Option::Some(#rest.to_string()) }
                },
                None => quote! { ::core::option::Option::None },
            };
            quote! {
                ::mettail_rholang_codegen::AcReconstructTemplate::Bag {
                    op: #op.to_string(),
                    elements: ::std::vec![#(#elements),*],
                    rest: #rest,
                }
            }
        },
        T::Binder { body } => {
            let body = ac_template_tokens_recursive(body);
            quote! {
                ::mettail_rholang_codegen::AcReconstructTemplate::Binder {
                    body: ::std::boxed::Box::new(#body),
                }
            }
        },
    }
}

#[test]
fn ac_template_token_pda_matches_recursive_equation() {
    let fixture = T::Bag {
        op: "PPar".to_string(),
        elements: vec![
            T::Var("left".to_string()),
            T::Node {
                constructor: "POutput".to_string(),
                children: vec![
                    T::Binder {
                        body: Box::new(T::Var("body".to_string())),
                    },
                    T::Bag {
                        op: "Nested".to_string(),
                        elements: vec![T::Var("value".to_string())],
                        rest: None,
                    },
                ],
            },
        ],
        rest: Some("tail".to_string()),
    };
    assert_eq!(
        ac_template_tokens(&fixture).to_string(),
        ac_template_tokens_recursive(&fixture).to_string()
    );
}

#[test]
fn ac_template_token_pda_handles_20k_nesting_on_a_256k_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut template = T::Var("leaf".to_string());
            for _ in 0..20_000 {
                template = T::Binder { body: Box::new(template) };
            }
            let tokens = ac_template_tokens(&template);
            assert!(crate::gen::token_tree_walk::TokenTreeLeaves::new(tokens).any(|token| {
                matches!(token, proc_macro2::TokenTree::Literal(literal) if literal.to_string() == "\"leaf\"")
            }));
        })
        .expect("spawn low-stack AC-template emitter gate")
        .join()
        .expect("AC-template emitter must not consume nesting-proportional native stack");
}
