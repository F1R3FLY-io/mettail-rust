use super::*;
use proc_macro2::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span};

fn collect_recursive(tokens: TokenStream, out: &mut Vec<String>) {
    for token in tokens {
        match token {
            TokenTree::Group(group) => collect_recursive(group.stream(), out),
            TokenTree::Ident(ident) => out.push(format!("ident:{ident}")),
            TokenTree::Punct(punct) => {
                out.push(format!("punct:{}:{:?}", punct.as_char(), punct.spacing()))
            },
            TokenTree::Literal(literal) => out.push(format!("literal:{literal}")),
        }
    }
}

fn describe(token: TokenTree) -> String {
    match token {
        TokenTree::Ident(ident) => format!("ident:{ident}"),
        TokenTree::Punct(punct) => format!("punct:{}:{:?}", punct.as_char(), punct.spacing()),
        TokenTree::Literal(literal) => format!("literal:{literal}"),
        TokenTree::Group(_) => unreachable!("leaf iterator yielded a group"),
    }
}

#[test]
fn token_tree_leaf_iterator_matches_recursive_preorder() {
    let inner: TokenStream = [
        TokenTree::Ident(Ident::new("Inner", Span::call_site())),
        TokenTree::Punct(Punct::new(',', Spacing::Alone)),
        TokenTree::Literal(Literal::u64_suffixed(7)),
    ]
    .into_iter()
    .collect();
    let fixture: TokenStream = [
        TokenTree::Ident(Ident::new("Outer", Span::call_site())),
        TokenTree::Group(Group::new(Delimiter::Brace, inner)),
        TokenTree::Literal(Literal::string("tail")),
    ]
    .into_iter()
    .collect();
    let actual: Vec<_> = TokenTreeLeaves::new(fixture.clone())
        .map(describe)
        .collect();
    let mut expected = Vec::new();
    collect_recursive(fixture, &mut expected);
    assert_eq!(actual, expected);
}

#[test]
fn token_tree_leaf_iterator_handles_20k_groups_on_a_256k_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut tokens: TokenStream =
                std::iter::once(TokenTree::Ident(Ident::new("Leaf", Span::call_site()))).collect();
            for _ in 0..20_000 {
                tokens =
                    std::iter::once(TokenTree::Group(Group::new(Delimiter::Parenthesis, tokens)))
                        .collect();
            }
            let mut leaves = TokenTreeLeaves::new(tokens);
            assert!(matches!(leaves.next(), Some(TokenTree::Ident(ident)) if ident == "Leaf"));
            assert!(leaves.next().is_none());
            std::mem::forget(leaves);
        })
        .expect("spawn low-stack token-tree iterator gate")
        .join()
        .expect("token-tree iterator must not consume nesting-proportional native stack");
}
