//! Bounded recursive reference for regex token-tree rendering.

use super::*;
use proc_macro2::{Delimiter, Group, Ident, Span, TokenStream, TokenTree};

fn token_tree_to_string_recursive(tree: &TokenTree) -> String {
    match tree {
        TokenTree::Group(group) => {
            let (open, close) = match group.delimiter() {
                Delimiter::Parenthesis => ("(", ")"),
                Delimiter::Brace => ("{", "}"),
                Delimiter::Bracket => ("[", "]"),
                Delimiter::None => ("", ""),
            };
            let inner: String = group
                .stream()
                .into_iter()
                .map(|child| token_tree_to_string_recursive(&child))
                .collect();
            format!("{open}{inner}{close}")
        },
        TokenTree::Ident(ident) => ident.to_string(),
        TokenTree::Punct(punct) => punct.as_char().to_string(),
        TokenTree::Literal(literal) => literal.to_string(),
    }
}

#[test]
fn token_renderer_matches_the_bounded_recursive_equation() {
    let trees: Vec<_> = quote::quote! { ({alpha [beta]} + 42) }
        .into_iter()
        .collect();
    for (index, tree) in trees.iter().enumerate() {
        assert_eq!(
            token_tree_to_string(tree),
            token_tree_to_string_recursive(tree),
            "token tree {index}",
        );
    }
}

#[test]
fn token_renderer_is_stack_safe_at_depth_20k() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("token-render-256k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut tree = TokenTree::Ident(Ident::new("x", Span::call_site()));
            for _ in 0..DEPTH {
                tree = TokenTree::Group(Group::new(
                    Delimiter::Parenthesis,
                    TokenStream::from_iter([tree]),
                ));
            }
            let rendered = token_tree_to_string(&tree);
            assert_eq!(rendered.len(), 2 * DEPTH + 1);
            assert_eq!(rendered.as_bytes()[DEPTH], b'x');
            std::mem::forget(tree);
        })
        .expect("spawn token-render depth gate")
        .join()
        .expect("token renderer must not overflow or panic");
}
