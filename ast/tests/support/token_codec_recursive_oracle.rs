//! Bounded recursive references for the compact token-tree codec.

use super::*;
use proc_macro2::Ident;

fn encode_tree_recursive(tree: &TokenTree, output: &mut Vec<u8>) {
    match tree {
        TokenTree::Ident(ident) => {
            let name = ident.to_string();
            output.push(TAG_IDENT);
            output.extend_from_slice(&(name.len() as u16).to_le_bytes());
            output.extend_from_slice(name.as_bytes());
        },
        TokenTree::Punct(punct) => {
            output.push(TAG_PUNCT);
            output.push(punct.as_char() as u8);
            output.push(match punct.spacing() {
                Spacing::Alone => SPACING_ALONE,
                Spacing::Joint => SPACING_JOINT,
            });
        },
        TokenTree::Literal(literal) => {
            let repr = literal.to_string();
            output.push(TAG_LITERAL);
            output.extend_from_slice(&(repr.len() as u16).to_le_bytes());
            output.extend_from_slice(repr.as_bytes());
        },
        TokenTree::Group(group) => {
            output.push(match group.delimiter() {
                Delimiter::Parenthesis => TAG_GROUP_PAREN,
                Delimiter::Brace => TAG_GROUP_BRACE,
                Delimiter::Bracket => TAG_GROUP_BRACKET,
                Delimiter::None => TAG_GROUP_NONE,
            });
            let mut children = Vec::new();
            for child in group.stream() {
                encode_tree_recursive(&child, &mut children);
            }
            output.extend_from_slice(&(children.len() as u32).to_le_bytes());
            output.extend_from_slice(&children);
        },
    }
}

fn encode_recursive(stream: &TokenStream) -> Vec<u8> {
    let mut output = Vec::new();
    for tree in stream.clone() {
        encode_tree_recursive(&tree, &mut output);
    }
    output
}

fn read_recursive<'a>(bytes: &'a [u8], cursor: &mut usize, len: usize) -> &'a [u8] {
    let start = *cursor;
    *cursor += len;
    &bytes[start..*cursor]
}

fn decode_tree_recursive(bytes: &[u8], cursor: &mut usize) -> TokenTree {
    let tag = read_recursive(bytes, cursor, 1)[0];
    match tag {
        TAG_IDENT => {
            let raw = read_recursive(bytes, cursor, 2);
            let len = u16::from_le_bytes([raw[0], raw[1]]) as usize;
            let name = std::str::from_utf8(read_recursive(bytes, cursor, len)).unwrap();
            TokenTree::Ident(Ident::new(name, Span::call_site()))
        },
        TAG_PUNCT => {
            let ch = read_recursive(bytes, cursor, 1)[0] as char;
            let spacing = match read_recursive(bytes, cursor, 1)[0] {
                SPACING_ALONE => Spacing::Alone,
                SPACING_JOINT => Spacing::Joint,
                other => panic!("oracle spacing byte {other}"),
            };
            TokenTree::Punct(Punct::new(ch, spacing))
        },
        TAG_LITERAL => {
            let raw = read_recursive(bytes, cursor, 2);
            let len = u16::from_le_bytes([raw[0], raw[1]]) as usize;
            let repr = std::str::from_utf8(read_recursive(bytes, cursor, len)).unwrap();
            TokenTree::Literal(repr.parse().unwrap())
        },
        TAG_GROUP_PAREN | TAG_GROUP_BRACE | TAG_GROUP_BRACKET | TAG_GROUP_NONE => {
            let delimiter = match tag {
                TAG_GROUP_PAREN => Delimiter::Parenthesis,
                TAG_GROUP_BRACE => Delimiter::Brace,
                TAG_GROUP_BRACKET => Delimiter::Bracket,
                TAG_GROUP_NONE => Delimiter::None,
                _ => unreachable!(),
            };
            let raw = read_recursive(bytes, cursor, 4);
            let len = u32::from_le_bytes([raw[0], raw[1], raw[2], raw[3]]) as usize;
            let end = *cursor + len;
            let mut children = Vec::new();
            while *cursor < end {
                children.push(decode_tree_recursive(bytes, cursor));
            }
            assert_eq!(*cursor, end);
            TokenTree::Group(Group::new(delimiter, TokenStream::from_iter(children)))
        },
        other => panic!("oracle tag byte {other:#x}"),
    }
}

fn decode_recursive(bytes: &[u8]) -> TokenStream {
    let mut cursor = 0;
    let mut trees = Vec::new();
    while cursor < bytes.len() {
        trees.push(decode_tree_recursive(bytes, &mut cursor));
    }
    TokenStream::from_iter(trees)
}

#[test]
fn token_codec_matches_the_bounded_recursive_equations() {
    let corpus = [
        quote::quote! {},
        quote::quote! { alpha += 42 },
        quote::quote! { fn(alpha: [i32]) { beta(alpha) } },
        quote::quote! { ((({[gamma]}))) },
    ];
    for (index, stream) in corpus.iter().enumerate() {
        let encoded = encode(stream).expect("corpus token stream must encode");
        assert_eq!(encoded, encode_recursive(stream), "encoded corpus item {index}");
        assert_eq!(
            decode(&encoded)
                .expect("recursive-oracle bytes must decode")
                .to_string(),
            decode_recursive(&encoded).to_string(),
            "decoded corpus item {index}",
        );
    }
}

#[test]
fn token_codec_rejects_a_group_that_crosses_its_parent_boundary() {
    let malformed = [TAG_GROUP_PAREN, 2, 0, 0, 0, TAG_IDENT];
    let error = decode(&malformed).expect_err("cross-boundary group must be rejected");
    assert_eq!(error.offset, 1);
    assert!(error.message.contains("crosses its parent boundary"));
}

#[test]
fn token_codec_reports_the_wire_literal_length_bound_without_truncation() {
    let stream = TokenStream::from_iter([TokenTree::Literal(Literal::string(&"x".repeat(70_000)))]);
    let error = encode(&stream).expect_err("oversized literal must not truncate its length");
    assert_eq!(error.offset, 0);
    assert!(error.message.contains("u16 length"));
}

#[test]
fn token_codec_is_stack_safe_at_depth_20k() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("token-codec-256k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut stream =
                TokenStream::from_iter([TokenTree::Ident(Ident::new("x", Span::call_site()))]);
            for _ in 0..DEPTH {
                stream = TokenStream::from_iter([TokenTree::Group(Group::new(
                    Delimiter::Parenthesis,
                    stream,
                ))]);
            }

            let encoded = encode(&stream).expect("deep token stream must encode");
            assert_eq!(encoded.len(), 4 + 5 * DEPTH);
            std::mem::forget(stream);

            let mut decoded = decode(&encoded).expect("deep token stream must decode");
            for _ in 0..DEPTH {
                let mut trees = decoded.into_iter();
                let Some(TokenTree::Group(group)) = trees.next() else {
                    panic!("token codec changed the nested group spine");
                };
                assert!(trees.next().is_none());
                decoded = group.stream();
            }
            let mut leaf = decoded.into_iter();
            assert!(matches!(leaf.next(), Some(TokenTree::Ident(ident)) if ident == "x"));
            assert!(leaf.next().is_none());
        })
        .expect("spawn token-codec depth gate")
        .join()
        .expect("token codec must not overflow or panic");
}
