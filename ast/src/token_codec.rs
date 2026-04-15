//! Compact binary TLV codec for `proc_macro2::TokenStream`.
//!
//! Serializes token trees to a flat `Vec<u8>` buffer that can be stored
//! across proc-macro invocations and decoded into fresh bridge-valid
//! `TokenStream` values in a later invocation.
//!
//! ## Wire Format
//!
//! Tag-Length-Value (TLV) encoding. All multi-byte integers are little-endian.
//! No alignment padding.
//!
//! ```text
//! Token ::= Ident | Punct | Literal | Group
//!
//! Ident:    0x01  len:u16le  name_bytes:[u8; len]
//! Punct:    0x02  char:u8    spacing:u8           // 0=Alone, 1=Joint
//! Literal:  0x03  len:u16le  repr_bytes:[u8; len] // Display representation
//! Group:    0x04+delim  byte_len:u32le  children:[u8; byte_len]
//!             delim offsets: Paren=0x04, Brace=0x05, Bracket=0x06, None=0x07
//!
//! Stream ::= Token*  (concatenated, self-delimiting via tags + lengths)
//! ```
//!
//! ## Span Policy
//!
//! All reconstructed tokens use `Span::call_site()`. Original spans from the
//! base language's bridge session are not preserved — they would be invalid
//! in the extension language's session and misleading in error messages.

use proc_macro2::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

// Tag bytes
const TAG_IDENT: u8 = 0x01;
const TAG_PUNCT: u8 = 0x02;
const TAG_LITERAL: u8 = 0x03;
const TAG_GROUP_PAREN: u8 = 0x04;
const TAG_GROUP_BRACE: u8 = 0x05;
const TAG_GROUP_BRACKET: u8 = 0x06;
const TAG_GROUP_NONE: u8 = 0x07;

// Spacing values
const SPACING_ALONE: u8 = 0;
const SPACING_JOINT: u8 = 1;

/// Encode a `TokenStream` into a compact binary buffer.
pub fn encode(stream: &TokenStream) -> Vec<u8> {
    let mut buf = Vec::new();
    for tree in stream.clone() {
        encode_tree(&tree, &mut buf);
    }
    buf
}

fn encode_tree(tree: &TokenTree, buf: &mut Vec<u8>) {
    match tree {
        TokenTree::Ident(ident) => {
            let name = ident.to_string();
            let name_bytes = name.as_bytes();
            buf.push(TAG_IDENT);
            buf.extend_from_slice(&(name_bytes.len() as u16).to_le_bytes());
            buf.extend_from_slice(name_bytes);
        }
        TokenTree::Punct(punct) => {
            buf.push(TAG_PUNCT);
            buf.push(punct.as_char() as u8);
            buf.push(match punct.spacing() {
                Spacing::Alone => SPACING_ALONE,
                Spacing::Joint => SPACING_JOINT,
            });
        }
        TokenTree::Literal(lit) => {
            let repr = lit.to_string();
            let repr_bytes = repr.as_bytes();
            buf.push(TAG_LITERAL);
            buf.extend_from_slice(&(repr_bytes.len() as u16).to_le_bytes());
            buf.extend_from_slice(repr_bytes);
        }
        TokenTree::Group(group) => {
            let tag = match group.delimiter() {
                Delimiter::Parenthesis => TAG_GROUP_PAREN,
                Delimiter::Brace => TAG_GROUP_BRACE,
                Delimiter::Bracket => TAG_GROUP_BRACKET,
                Delimiter::None => TAG_GROUP_NONE,
            };
            buf.push(tag);

            // Encode children into a temporary buffer to get byte length
            let mut children_buf = Vec::new();
            for child in group.stream() {
                encode_tree(&child, &mut children_buf);
            }

            buf.extend_from_slice(&(children_buf.len() as u32).to_le_bytes());
            buf.extend_from_slice(&children_buf);
        }
    }
}

/// Decode a binary buffer back into a fresh `TokenStream`.
///
/// All reconstructed tokens use `Span::call_site()` — they are valid
/// in the current proc-macro bridge session regardless of when the
/// bytes were originally produced.
pub fn decode(bytes: &[u8]) -> TokenStream {
    let mut cursor = Cursor { data: bytes, pos: 0 };
    let mut trees = Vec::new();
    while cursor.pos < cursor.data.len() {
        trees.push(decode_tree(&mut cursor));
    }
    TokenStream::from_iter(trees)
}

fn decode_tree(cursor: &mut Cursor<'_>) -> TokenTree {
    let tag = cursor.read_u8();
    match tag {
        TAG_IDENT => {
            let len = cursor.read_u16_le() as usize;
            let name_bytes = cursor.read_bytes(len);
            let name = std::str::from_utf8(name_bytes)
                .expect("token_codec: invalid UTF-8 in ident name");
            TokenTree::Ident(Ident::new(name, Span::call_site()))
        }
        TAG_PUNCT => {
            let ch = cursor.read_u8() as char;
            let spacing = match cursor.read_u8() {
                SPACING_ALONE => Spacing::Alone,
                SPACING_JOINT => Spacing::Joint,
                other => panic!("token_codec: invalid spacing byte: {}", other),
            };
            TokenTree::Punct(Punct::new(ch, spacing))
        }
        TAG_LITERAL => {
            let len = cursor.read_u16_le() as usize;
            let repr_bytes = cursor.read_bytes(len);
            let repr = std::str::from_utf8(repr_bytes)
                .expect("token_codec: invalid UTF-8 in literal repr");
            let lit: Literal = repr.parse()
                .unwrap_or_else(|e| panic!("token_codec: failed to parse literal '{}': {}", repr, e));
            TokenTree::Literal(lit)
        }
        TAG_GROUP_PAREN | TAG_GROUP_BRACE | TAG_GROUP_BRACKET | TAG_GROUP_NONE => {
            let delimiter = match tag {
                TAG_GROUP_PAREN => Delimiter::Parenthesis,
                TAG_GROUP_BRACE => Delimiter::Brace,
                TAG_GROUP_BRACKET => Delimiter::Bracket,
                TAG_GROUP_NONE => Delimiter::None,
                _ => unreachable!(),
            };
            let byte_len = cursor.read_u32_le() as usize;
            let children_bytes = cursor.read_bytes(byte_len);

            // Recursively decode children
            let mut child_cursor = Cursor { data: children_bytes, pos: 0 };
            let mut children = Vec::new();
            while child_cursor.pos < child_cursor.data.len() {
                children.push(decode_tree(&mut child_cursor));
            }

            let inner = TokenStream::from_iter(children);
            TokenTree::Group(Group::new(delimiter, inner))
        }
        other => panic!("token_codec: unknown tag byte: 0x{:02x}", other),
    }
}

/// Cursor for sequential byte reads during decoding.
struct Cursor<'a> {
    data: &'a [u8],
    pos: usize,
}

impl Cursor<'_> {
    fn read_u8(&mut self) -> u8 {
        let val = self.data[self.pos];
        self.pos += 1;
        val
    }

    fn read_u16_le(&mut self) -> u16 {
        let val = u16::from_le_bytes([self.data[self.pos], self.data[self.pos + 1]]);
        self.pos += 2;
        val
    }

    fn read_u32_le(&mut self) -> u32 {
        let val = u32::from_le_bytes([
            self.data[self.pos],
            self.data[self.pos + 1],
            self.data[self.pos + 2],
            self.data[self.pos + 3],
        ]);
        self.pos += 4;
        val
    }

    fn read_bytes(&mut self, len: usize) -> &[u8] {
        let slice = &self.data[self.pos..self.pos + len];
        self.pos += len;
        slice
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    #[test]
    fn roundtrip_ident() {
        let ts: TokenStream = quote! { foo };
        let bytes = encode(&ts);
        let decoded = decode(&bytes);
        assert_eq!(decoded.to_string(), "foo");
    }

    #[test]
    fn roundtrip_punct() {
        let ts: TokenStream = quote! { += };
        let bytes = encode(&ts);
        let decoded = decode(&bytes);
        // quote! { += } produces two Punct tokens: '+' (Joint) and '=' (Alone)
        let tokens: Vec<TokenTree> = decoded.into_iter().collect();
        assert_eq!(tokens.len(), 2);
        match &tokens[0] {
            TokenTree::Punct(p) => {
                assert_eq!(p.as_char(), '+');
                assert!(matches!(p.spacing(), Spacing::Joint));
            }
            other => panic!("expected Punct, got {:?}", other),
        }
        match &tokens[1] {
            TokenTree::Punct(p) => {
                assert_eq!(p.as_char(), '=');
                assert!(matches!(p.spacing(), Spacing::Alone));
            }
            other => panic!("expected Punct, got {:?}", other),
        }
    }

    #[test]
    fn roundtrip_literal_int() {
        let ts: TokenStream = quote! { 42 };
        let bytes = encode(&ts);
        let decoded = decode(&bytes);
        assert_eq!(decoded.to_string(), "42");
    }

    #[test]
    fn roundtrip_literal_string() {
        let ts: TokenStream = quote! { "hello" };
        let bytes = encode(&ts);
        let decoded = decode(&bytes);
        assert_eq!(decoded.to_string(), "\"hello\"");
    }

    #[test]
    fn roundtrip_literal_float() {
        let ts: TokenStream = quote! { 3.14 };
        let bytes = encode(&ts);
        let decoded = decode(&bytes);
        assert_eq!(decoded.to_string(), "3.14");
    }

    #[test]
    fn roundtrip_group_brace() {
        let ts: TokenStream = quote! { { a + b } };
        let bytes = encode(&ts);
        let decoded = decode(&bytes);
        // Normalize whitespace for comparison
        let original_str = ts.to_string().replace(' ', "");
        let decoded_str = decoded.to_string().replace(' ', "");
        assert_eq!(decoded_str, original_str);
    }

    #[test]
    fn roundtrip_nested_groups() {
        let ts: TokenStream = quote! { fn(x: [i32]) };
        let bytes = encode(&ts);
        let decoded = decode(&bytes);
        let original_str = ts.to_string().replace(' ', "");
        let decoded_str = decoded.to_string().replace(' ', "");
        assert_eq!(decoded_str, original_str);
    }

    #[test]
    fn roundtrip_empty_stream() {
        let ts = TokenStream::new();
        let bytes = encode(&ts);
        assert!(bytes.is_empty());
        let decoded = decode(&bytes);
        assert!(decoded.is_empty());
    }

    #[test]
    fn roundtrip_language_like_input() {
        // A simplified BaseMath-like token stream
        let ts: TokenStream = quote! {
            name: BaseMath,
            types {
                ![i32] as Num
            },
            terms {
                Add . a:Num, b:Num |- a "+" b : Num ![a + b] fold;
                Sub . a:Num, b:Num |- a "-" b : Num ![a - b] fold;
            },
            equations {
            },
            rewrites {
                AddCongL . | S ~> T |- (Add S R) ~> (Add T R);
            },
        };
        let bytes = encode(&ts);
        let decoded = decode(&bytes);

        // Verify it re-parses as a LanguageDef
        let parsed: syn::Result<super::super::language::LanguageDef> = syn::parse2(decoded);
        assert!(parsed.is_ok(), "re-parsed LanguageDef failed: {:?}", parsed.err());
        let lang = parsed.expect("just checked");
        assert_eq!(lang.name.to_string(), "BaseMath");
        assert_eq!(lang.types.len(), 1);
        assert_eq!(lang.terms.len(), 2);
        assert_eq!(lang.rewrites.len(), 1);
    }

    #[test]
    fn roundtrip_fragment_like_input() {
        let ts: TokenStream = quote! {
            name: IntArithFragment,
            types {
                ![i32] as Int
            },
            terms {
                AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
                SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
            }
        };
        let bytes = encode(&ts);
        let decoded = decode(&bytes);

        let parsed: syn::Result<super::super::fragment::FragmentDef> = syn::parse2(decoded);
        assert!(parsed.is_ok(), "re-parsed FragmentDef failed: {:?}", parsed.err());
        let frag = parsed.expect("just checked");
        assert_eq!(frag.name.to_string(), "IntArithFragment");
        assert_eq!(frag.types.len(), 1);
        assert_eq!(frag.terms.len(), 2);
    }
}
