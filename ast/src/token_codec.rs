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

use proc_macro2::{Delimiter, Group, Literal, Punct, Spacing, Span, TokenStream, TokenTree};
use std::fmt;

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

/// A compact token-codec failure, anchored at the input or output byte offset where it occurred.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenCodecError {
    pub offset: usize,
    pub message: String,
}

impl TokenCodecError {
    fn new(offset: usize, message: impl Into<String>) -> Self {
        Self { offset, message: message.into() }
    }
}

impl fmt::Display for TokenCodecError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "byte {}: {}", self.offset, self.message)
    }
}

impl std::error::Error for TokenCodecError {}

/// Encode a `TokenStream` into a compact binary buffer, reporting explicit format bounds.
pub fn encode(stream: &TokenStream) -> Result<Vec<u8>, TokenCodecError> {
    let mut buf = Vec::new();
    enum EncodeJob {
        Visit(TokenTree),
        FinishGroup {
            length_offset: usize,
            children_offset: usize,
        },
    }

    let roots: Vec<_> = stream.clone().into_iter().collect();
    let mut jobs: Vec<_> = roots.into_iter().rev().map(EncodeJob::Visit).collect();
    while let Some(job) = jobs.pop() {
        match job {
            EncodeJob::Visit(TokenTree::Ident(ident)) => {
                let name = ident.to_string();
                let name_bytes = name.as_bytes();
                let length = u16::try_from(name_bytes.len()).map_err(|_| {
                    TokenCodecError::new(
                        buf.len(),
                        "identifier representation exceeds the wire-format u16 length",
                    )
                })?;
                buf.push(TAG_IDENT);
                buf.extend_from_slice(&length.to_le_bytes());
                buf.extend_from_slice(name_bytes);
            },
            EncodeJob::Visit(TokenTree::Punct(punct)) => {
                buf.push(TAG_PUNCT);
                buf.push(punct.as_char() as u8);
                buf.push(match punct.spacing() {
                    Spacing::Alone => SPACING_ALONE,
                    Spacing::Joint => SPACING_JOINT,
                });
            },
            EncodeJob::Visit(TokenTree::Literal(literal)) => {
                let repr = literal.to_string();
                let repr_bytes = repr.as_bytes();
                let length = u16::try_from(repr_bytes.len()).map_err(|_| {
                    TokenCodecError::new(
                        buf.len(),
                        "literal representation exceeds the wire-format u16 length",
                    )
                })?;
                buf.push(TAG_LITERAL);
                buf.extend_from_slice(&length.to_le_bytes());
                buf.extend_from_slice(repr_bytes);
            },
            EncodeJob::Visit(TokenTree::Group(group)) => {
                let tag = match group.delimiter() {
                    Delimiter::Parenthesis => TAG_GROUP_PAREN,
                    Delimiter::Brace => TAG_GROUP_BRACE,
                    Delimiter::Bracket => TAG_GROUP_BRACKET,
                    Delimiter::None => TAG_GROUP_NONE,
                };
                buf.push(tag);
                let length_offset = buf.len();
                buf.extend_from_slice(&0_u32.to_le_bytes());
                let children_offset = buf.len();
                jobs.push(EncodeJob::FinishGroup { length_offset, children_offset });
                let children: Vec<_> = group.stream().into_iter().collect();
                jobs.extend(children.into_iter().rev().map(EncodeJob::Visit));
            },
            EncodeJob::FinishGroup { length_offset, children_offset } => {
                let length = u32::try_from(buf.len() - children_offset).map_err(|_| {
                    TokenCodecError::new(
                        length_offset,
                        "encoded group exceeds the wire-format u32 length",
                    )
                })?;
                buf[length_offset..length_offset + 4].copy_from_slice(&length.to_le_bytes());
            },
        }
    }
    Ok(buf)
}

/// Decode a binary buffer back into a fresh `TokenStream`, rejecting malformed input.
///
/// All reconstructed tokens use `Span::call_site()` — they are valid
/// in the current proc-macro bridge session regardless of when the
/// bytes were originally produced.
pub fn decode(bytes: &[u8]) -> Result<TokenStream, TokenCodecError> {
    let mut cursor = Cursor { data: bytes, pos: 0 };
    struct DecodeFrame {
        end: usize,
        delimiter: Option<Delimiter>,
        trees: Vec<TokenTree>,
    }

    let mut frames = vec![DecodeFrame {
        end: bytes.len(),
        delimiter: None,
        trees: Vec::new(),
    }];
    loop {
        let frame_end = frames
            .last()
            .ok_or_else(|| TokenCodecError::new(cursor.pos, "missing root frame"))?
            .end;
        if cursor.pos == frame_end {
            let completed = frames
                .pop()
                .ok_or_else(|| TokenCodecError::new(cursor.pos, "missing completed frame"))?;
            let stream = TokenStream::from_iter(completed.trees);
            if let Some(delimiter) = completed.delimiter {
                frames
                    .last_mut()
                    .ok_or_else(|| {
                        TokenCodecError::new(cursor.pos, "group frame has no parent frame")
                    })?
                    .trees
                    .push(TokenTree::Group(Group::new(delimiter, stream)));
                continue;
            }
            debug_assert!(frames.is_empty());
            return Ok(stream);
        }
        if cursor.pos > frame_end {
            return Err(TokenCodecError::new(
                cursor.pos,
                "child stream crossed its declared group boundary",
            ));
        }

        let tag = cursor.read_u8(frame_end)?;
        let tree = match tag {
            TAG_IDENT => {
                let len = cursor.read_u16_le(frame_end)? as usize;
                let name_offset = cursor.pos;
                let name_bytes = cursor.read_bytes(len, frame_end)?;
                let name = std::str::from_utf8(name_bytes).map_err(|error| {
                    TokenCodecError::new(name_offset, format!("invalid identifier UTF-8: {error}"))
                })?;
                let tokens: TokenStream = name.parse().map_err(|error| {
                    TokenCodecError::new(
                        name_offset,
                        format!("invalid identifier representation {name:?}: {error}"),
                    )
                })?;
                let mut tokens = tokens.into_iter();
                let Some(TokenTree::Ident(mut ident)) = tokens.next() else {
                    return Err(TokenCodecError::new(
                        name_offset,
                        format!("identifier representation {name:?} is not one identifier"),
                    ));
                };
                if tokens.next().is_some() {
                    return Err(TokenCodecError::new(
                        name_offset,
                        format!("identifier representation {name:?} contains multiple tokens"),
                    ));
                }
                ident.set_span(Span::call_site());
                Some(TokenTree::Ident(ident))
            },
            TAG_PUNCT => {
                let punct_offset = cursor.pos;
                let ch = cursor.read_u8(frame_end)? as char;
                if !matches!(
                    ch,
                    '=' | '<'
                        | '>'
                        | '-'
                        | '!'
                        | '~'
                        | '+'
                        | '*'
                        | '/'
                        | '%'
                        | '^'
                        | '&'
                        | '|'
                        | '@'
                        | '.'
                        | ','
                        | ';'
                        | ':'
                        | '#'
                        | '$'
                        | '?'
                        | '\''
                ) {
                    return Err(TokenCodecError::new(
                        punct_offset,
                        format!("invalid punctuation character {ch:?}"),
                    ));
                }
                let spacing = match cursor.read_u8(frame_end)? {
                    SPACING_ALONE => Spacing::Alone,
                    SPACING_JOINT => Spacing::Joint,
                    other => {
                        return Err(TokenCodecError::new(
                            cursor.pos - 1,
                            format!("invalid spacing byte {other}"),
                        ));
                    },
                };
                Some(TokenTree::Punct(Punct::new(ch, spacing)))
            },
            TAG_LITERAL => {
                let len = cursor.read_u16_le(frame_end)? as usize;
                let repr_offset = cursor.pos;
                let repr_bytes = cursor.read_bytes(len, frame_end)?;
                let repr = std::str::from_utf8(repr_bytes).map_err(|error| {
                    TokenCodecError::new(repr_offset, format!("invalid literal UTF-8: {error}"))
                })?;
                let literal: Literal = repr.parse().map_err(|error| {
                    TokenCodecError::new(
                        repr_offset,
                        format!("failed to parse literal {repr:?}: {error}"),
                    )
                })?;
                Some(TokenTree::Literal(literal))
            },
            TAG_GROUP_PAREN | TAG_GROUP_BRACE | TAG_GROUP_BRACKET | TAG_GROUP_NONE => {
                let delimiter = match tag {
                    TAG_GROUP_PAREN => Delimiter::Parenthesis,
                    TAG_GROUP_BRACE => Delimiter::Brace,
                    TAG_GROUP_BRACKET => Delimiter::Bracket,
                    TAG_GROUP_NONE => Delimiter::None,
                    other => {
                        return Err(TokenCodecError::new(
                            cursor.pos - 1,
                            format!("unknown group delimiter tag {other:#04x}"),
                        ));
                    },
                };
                let byte_len = cursor.read_u32_le(frame_end)? as usize;
                let end = cursor.pos.checked_add(byte_len).ok_or_else(|| {
                    TokenCodecError::new(cursor.pos, "group length overflows usize")
                })?;
                if end > frame_end {
                    return Err(TokenCodecError::new(
                        cursor.pos - 4,
                        "group length crosses its parent boundary",
                    ));
                }
                frames.push(DecodeFrame {
                    end,
                    delimiter: Some(delimiter),
                    trees: Vec::new(),
                });
                None
            },
            other => {
                return Err(TokenCodecError::new(
                    cursor.pos - 1,
                    format!("unknown tag byte {other:#04x}"),
                ));
            },
        };
        if let Some(tree) = tree {
            frames
                .last_mut()
                .ok_or_else(|| TokenCodecError::new(cursor.pos, "leaf has no parent frame"))?
                .trees
                .push(tree);
        }
    }
}

/// Cursor for sequential byte reads during decoding.
struct Cursor<'a> {
    data: &'a [u8],
    pos: usize,
}

impl Cursor<'_> {
    fn require(&self, len: usize, limit: usize) -> Result<(), TokenCodecError> {
        let end = self
            .pos
            .checked_add(len)
            .ok_or_else(|| TokenCodecError::new(self.pos, "cursor length overflows usize"))?;
        if end > limit {
            return Err(TokenCodecError::new(self.pos, "truncated token within group boundary"));
        }
        Ok(())
    }

    fn read_u8(&mut self, limit: usize) -> Result<u8, TokenCodecError> {
        self.require(1, limit)?;
        let val = self.data[self.pos];
        self.pos += 1;
        Ok(val)
    }

    fn read_u16_le(&mut self, limit: usize) -> Result<u16, TokenCodecError> {
        self.require(2, limit)?;
        let val = u16::from_le_bytes([self.data[self.pos], self.data[self.pos + 1]]);
        self.pos += 2;
        Ok(val)
    }

    fn read_u32_le(&mut self, limit: usize) -> Result<u32, TokenCodecError> {
        self.require(4, limit)?;
        let val = u32::from_le_bytes([
            self.data[self.pos],
            self.data[self.pos + 1],
            self.data[self.pos + 2],
            self.data[self.pos + 3],
        ]);
        self.pos += 4;
        Ok(val)
    }

    fn read_bytes(&mut self, len: usize, limit: usize) -> Result<&[u8], TokenCodecError> {
        self.require(len, limit)?;
        let slice = &self.data[self.pos..self.pos + len];
        self.pos += len;
        Ok(slice)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    #[test]
    fn roundtrip_ident() {
        let ts: TokenStream = quote! { foo };
        let bytes = encode(&ts).expect("test token stream must encode");
        let decoded = decode(&bytes).expect("encoded test bytes must decode");
        assert_eq!(decoded.to_string(), "foo");
    }

    #[test]
    fn roundtrip_punct() {
        let ts: TokenStream = quote! { += };
        let bytes = encode(&ts).expect("test token stream must encode");
        let decoded = decode(&bytes).expect("encoded test bytes must decode");
        // quote! { += } produces two Punct tokens: '+' (Joint) and '=' (Alone)
        let tokens: Vec<TokenTree> = decoded.into_iter().collect();
        assert_eq!(tokens.len(), 2);
        match &tokens[0] {
            TokenTree::Punct(p) => {
                assert_eq!(p.as_char(), '+');
                assert!(matches!(p.spacing(), Spacing::Joint));
            },
            other => panic!("expected Punct, got {:?}", other),
        }
        match &tokens[1] {
            TokenTree::Punct(p) => {
                assert_eq!(p.as_char(), '=');
                assert!(matches!(p.spacing(), Spacing::Alone));
            },
            other => panic!("expected Punct, got {:?}", other),
        }
    }

    #[test]
    fn roundtrip_literal_int() {
        let ts: TokenStream = quote! { 42 };
        let bytes = encode(&ts).expect("test token stream must encode");
        let decoded = decode(&bytes).expect("encoded test bytes must decode");
        assert_eq!(decoded.to_string(), "42");
    }

    #[test]
    fn roundtrip_literal_string() {
        let ts: TokenStream = quote! { "hello" };
        let bytes = encode(&ts).expect("test token stream must encode");
        let decoded = decode(&bytes).expect("encoded test bytes must decode");
        assert_eq!(decoded.to_string(), "\"hello\"");
    }

    #[test]
    fn roundtrip_literal_float() {
        let ts: TokenStream = quote! { 3.14 };
        let bytes = encode(&ts).expect("test token stream must encode");
        let decoded = decode(&bytes).expect("encoded test bytes must decode");
        assert_eq!(decoded.to_string(), "3.14");
    }

    #[test]
    fn roundtrip_group_brace() {
        let ts: TokenStream = quote! { { a + b } };
        let bytes = encode(&ts).expect("test token stream must encode");
        let decoded = decode(&bytes).expect("encoded test bytes must decode");
        // Normalize whitespace for comparison
        let original_str = ts.to_string().replace(' ', "");
        let decoded_str = decoded.to_string().replace(' ', "");
        assert_eq!(decoded_str, original_str);
    }

    #[test]
    fn roundtrip_nested_groups() {
        let ts: TokenStream = quote! { fn(x: [i32]) };
        let bytes = encode(&ts).expect("test token stream must encode");
        let decoded = decode(&bytes).expect("encoded test bytes must decode");
        let original_str = ts.to_string().replace(' ', "");
        let decoded_str = decoded.to_string().replace(' ', "");
        assert_eq!(decoded_str, original_str);
    }

    #[test]
    fn roundtrip_empty_stream() {
        let ts = TokenStream::new();
        let bytes = encode(&ts).expect("test token stream must encode");
        assert!(bytes.is_empty());
        let decoded = decode(&bytes).expect("encoded test bytes must decode");
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
        let bytes = encode(&ts).expect("test token stream must encode");
        let decoded = decode(&bytes).expect("encoded test bytes must decode");

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
        let bytes = encode(&ts).expect("test token stream must encode");
        let decoded = decode(&bytes).expect("encoded test bytes must decode");

        let parsed: syn::Result<super::super::fragment::FragmentDef> = syn::parse2(decoded);
        assert!(parsed.is_ok(), "re-parsed FragmentDef failed: {:?}", parsed.err());
        let frag = parsed.expect("just checked");
        assert_eq!(frag.name.to_string(), "IntArithFragment");
        assert_eq!(frag.types.len(), 1);
        assert_eq!(frag.terms.len(), 2);
    }
}

#[cfg(test)]
#[path = "../tests/support/token_codec_recursive_oracle.rs"]
mod recursive_oracle;
