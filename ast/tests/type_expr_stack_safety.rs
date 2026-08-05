use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};

fn nested_arrow_tokens(depth: usize) -> TokenStream {
    let leaf = || TokenTree::Ident(Ident::new("T", Span::call_site()));
    let mut tokens = TokenStream::from(leaf());
    for _ in 0..depth {
        let inner = [
            tokens,
            TokenStream::from_iter([
                TokenTree::Punct(Punct::new('-', Spacing::Joint)),
                TokenTree::Punct(Punct::new('>', Spacing::Alone)),
            ]),
            TokenStream::from(leaf()),
        ]
        .into_iter()
        .collect();
        tokens = TokenStream::from(TokenTree::Group(Group::new(Delimiter::Bracket, inner)));
    }
    tokens
}

#[test]
fn pathmap_type_uses_the_native_collection_variant() {
    let parsed = syn::parse_str::<TypeExpr>("PathMap(Proc)").expect("PathMap type must parse");
    assert!(matches!(
        &parsed,
        TypeExpr::Collection { coll_type: CollectionType::PathMap, element }
            if matches!(element.as_ref(), TypeExpr::Base(name) if name == "Proc")
    ));
    assert_eq!(parsed.to_string(), "PathMap(Proc)");
}

#[test]
fn nested_type_parse_fits_on_a_small_native_stack() {
    // proc_macro2/syn must first materialize and enter the compiler-owned
    // delimiter tree before TypeExpr's PDA receives it. This gate therefore
    // uses half Rust's ordinary 2 MiB thread stack; the 256 KiB lifecycle gate
    // below isolates the repository-owned traversal itself.
    const DEPTH: usize = 512;
    let handle = std::thread::Builder::new()
        .name("type-expr-small-stack".into())
        .stack_size(1024 * 1024)
        .spawn(|| {
            let tokens = nested_arrow_tokens(DEPTH);
            let parsed = syn::parse2::<TypeExpr>(tokens).expect("deep arrow type must parse");
            assert!(matches!(parsed, TypeExpr::Arrow { .. }));
            drop(parsed);
        })
        .expect("small-stack TypeExpr parser thread must spawn");
    handle
        .join()
        .expect("TypeExpr parsing must not overflow the native stack");
}

#[test]
fn deep_type_lifecycle_fits_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("type-expr-lifecycle-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut parsed = TypeExpr::Base(Ident::new("T", Span::call_site()));
            for _ in 0..DEPTH {
                parsed = TypeExpr::Arrow {
                    domain: Box::new(parsed),
                    codomain: Box::new(TypeExpr::Base(Ident::new("T", Span::call_site()))),
                };
            }
            let cloned = parsed.clone();
            assert_eq!(parsed, cloned);
            let display = parsed.to_string();
            assert!(display.starts_with("[[["));
            assert!(display.ends_with(" -> T]"));
            let debug = format!("{parsed:?}");
            assert!(debug.starts_with("Arrow { domain: Arrow { domain:"));
            assert!(debug.ends_with(" }"));
            drop(cloned);
            drop(parsed);
        })
        .expect("small-stack TypeExpr lifecycle thread must spawn");
    handle
        .join()
        .expect("TypeExpr lifecycle must not overflow the native stack");
}
