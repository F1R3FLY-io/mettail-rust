//! Original macro token-declaration projection, shared with source frontends.
//! Reader calls stay at their original branch sites. Final construction belongs
//! to the frontend: the token-kind writer does not read execution priority,
//! decoder, mode transition, or constructor code.

use crate::{AuthoredTokenOrigins, CustomTokenSpec, LiteralPatterns};
use mettail_grammar_core::NativeKind;

/// Exactly the custom-token fields observed by the active token-kind writer.
pub trait TokenMetadata {
    fn name(&self) -> &str;
    fn payload_type(&self) -> Option<&str>;
    fn is_builtin_override(&self) -> bool;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenDeclarationFields {
    pub name: String,
    pub payload_type: Option<String>,
    pub is_builtin_override: bool,
}

impl TokenMetadata for TokenDeclarationFields {
    fn name(&self) -> &str {
        &self.name
    }
    fn payload_type(&self) -> Option<&str> {
        self.payload_type.as_deref()
    }
    fn is_builtin_override(&self) -> bool {
        self.is_builtin_override
    }
}

impl TokenMetadata for CustomTokenSpec {
    fn name(&self) -> &str {
        &self.name
    }
    fn payload_type(&self) -> Option<&str> {
        self.payload_type.as_deref()
    }
    fn is_builtin_override(&self) -> bool {
        self.is_builtin_override
    }
}

pub trait TokenDeclarationReader {
    type Token: Copy;
    type Output;
    fn name(&self, token: Self::Token) -> String;
    fn native_kind(&self, token: Self::Token) -> Option<NativeKind>;
    fn pattern(&self, token: Self::Token) -> String;
    fn from_literals(&self, token: Self::Token) -> bool;
    fn category_native_type(&self, token: Self::Token) -> Option<String>;
    fn finish(&self, token: Self::Token, fields: TokenDeclarationFields) -> Self::Output;
}

/// The original global declaration loop and ordered integer-pattern union.
pub fn project_global_tokens<R: TokenDeclarationReader>(
    reader: &R,
    tokens: impl IntoIterator<Item = R::Token>,
) -> (LiteralPatterns, AuthoredTokenOrigins, Vec<R::Output>) {
    let mut literal_patterns = LiteralPatterns::default();
    let mut integer_alternatives = Vec::new();
    let mut origins = AuthoredTokenOrigins::default();
    let custom_tokens = tokens
        .into_iter()
        .enumerate()
        .map(|(source_index, token)| {
            let name = reader.name(token);
            let native_kind = reader.native_kind(token);
            let builtin_family = native_kind.and_then(|kind| kind.standard_token_variant());
            let is_builtin = builtin_family.is_some();
            origins.builtin_overrides.push(builtin_family);
            if let Some(kind) = native_kind {
                if is_builtin {
                    if kind.is_integer() {
                        integer_alternatives.push(reader.pattern(token));
                    } else {
                        match kind {
                            NativeKind::Float32 | NativeKind::Float64 => {
                                literal_patterns.float = reader.pattern(token);
                            },
                            NativeKind::Bool => {
                                literal_patterns.boolean = Some(reader.pattern(token));
                            },
                            NativeKind::Str => literal_patterns.string = reader.pattern(token),
                            _ => {},
                        }
                    }
                } else if reader.from_literals(token) {
                    match kind {
                        NativeKind::CanonicalBigRat => {
                            literal_patterns
                                .rational_by_category
                                .insert(name.clone(), reader.pattern(token));
                            origins
                                .typed_literals
                                .insert(("Rational".into(), name.clone()), source_index);
                        },
                        NativeKind::CanonicalFixedPoint => {
                            literal_patterns
                                .fixed_by_category
                                .insert(name.clone(), reader.pattern(token));
                            origins
                                .typed_literals
                                .insert(("FixedPoint".into(), name.clone()), source_index);
                        },
                        _ => {},
                    }
                }
            }
            if !is_builtin && reader.from_literals(token) && name == "Ident" {
                literal_patterns.ident = reader.pattern(token);
            }
            let payload_type = if reader.from_literals(token) {
                if is_builtin {
                    reader.category_native_type(token)
                } else {
                    Some("str".to_string())
                }
            } else {
                reader.category_native_type(token)
            };
            reader.finish(
                token,
                TokenDeclarationFields {
                    name,
                    payload_type,
                    is_builtin_override: is_builtin,
                },
            )
        })
        .collect();
    if !integer_alternatives.is_empty() {
        literal_patterns.integer = integer_alternatives
            .iter()
            .map(|p| format!("({})", p))
            .collect::<Vec<_>>()
            .join("|");
    }
    (literal_patterns, origins, custom_tokens)
}

/// The original named-mode token projection; modes cannot override builtins.
pub fn project_mode_token<R: TokenDeclarationReader>(reader: &R, token: R::Token) -> R::Output {
    let payload_type = if reader.from_literals(token) {
        Some("str".to_string())
    } else {
        reader.category_native_type(token)
    };
    reader.finish(
        token,
        TokenDeclarationFields {
            name: reader.name(token),
            payload_type,
            is_builtin_override: false,
        },
    )
}

/// Original literal-pattern input preparation from pipeline/wfst_emit.rs.
pub fn prepare_literal_patterns(input: &mut crate::lexer::LexerInput, patterns: &LiteralPatterns) {
    input.literal_patterns = patterns.clone();
    if !input.literal_patterns.rational_by_category.is_empty() {
        input.needs.rational = true;
    }
    if !input.literal_patterns.fixed_by_category.is_empty() {
        input.needs.fixed_point = true;
    }
    if patterns.boolean.is_some() {
        input.terminals.retain(|t| {
            !matches!(t.kind, crate::automata::TokenKind::True | crate::automata::TokenKind::False)
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    struct Reader {
        trace: RefCell<Vec<&'static str>>,
    }
    impl TokenDeclarationReader for Reader {
        type Token = usize;
        type Output = TokenDeclarationFields;
        fn name(&self, _: usize) -> String {
            self.trace.borrow_mut().push("name");
            "Integer".into()
        }
        fn native_kind(&self, _: usize) -> Option<NativeKind> {
            self.trace.borrow_mut().push("native");
            Some(NativeKind::Int32)
        }
        fn pattern(&self, token: usize) -> String {
            self.trace.borrow_mut().push("pattern");
            format!("pattern{token}")
        }
        fn from_literals(&self, _: usize) -> bool {
            self.trace.borrow_mut().push("literal");
            true
        }
        fn category_native_type(&self, _: usize) -> Option<String> {
            self.trace.borrow_mut().push("payload");
            Some("i32".into())
        }
        fn finish(&self, _: usize, fields: TokenDeclarationFields) -> Self::Output {
            self.trace.borrow_mut().push("finish");
            fields
        }
    }

    #[test]
    fn token_declaration_integer_union_and_reader_order_are_original() {
        let reader = Reader { trace: RefCell::new(Vec::new()) };
        let (patterns, origins, tokens) = project_global_tokens(&reader, [0, 1]);
        assert_eq!(patterns.integer, "(pattern0)|(pattern1)");
        assert_eq!(origins.builtin_overrides, [Some("Integer"), Some("Integer")]);
        assert!(
            tokens
                .iter()
                .all(|token| token.is_builtin_override
                    && token.payload_type.as_deref() == Some("i32"))
        );
        assert_eq!(
            *reader.trace.borrow(),
            [
                "name", "native", "pattern", "literal", "payload", "finish", "name", "native",
                "pattern", "literal", "payload", "finish"
            ]
        );
    }

    #[test]
    fn token_declaration_mode_does_not_observe_native_or_override_builtin() {
        let reader = Reader { trace: RefCell::new(Vec::new()) };
        let token = project_mode_token(&reader, 0);
        assert!(!token.is_builtin_override);
        assert_eq!(token.payload_type.as_deref(), Some("str"));
        assert_eq!(*reader.trace.borrow(), ["literal", "name", "finish"]);
    }

    #[test]
    fn original_terminal_observation_worker_preserves_empty_and_optional_distinctions() {
        use crate::lexer::{collect_terminal_observations, TerminalObservation as O};
        let empty = String::new();
        let separator = "::".to_owned();
        let key_value = "=>".to_owned();
        assert!(collect_terminal_observations([O::Collection {
            separator: &empty,
            key_val_separator: None
        }])
        .is_empty());
        assert_eq!(collect_terminal_observations([O::Terminal(&empty)]), [empty.clone()]);
        assert_eq!(
            collect_terminal_observations([
                O::Collection {
                    separator: &separator,
                    key_val_separator: Some(&key_value)
                },
                O::BinderCollection { separator: &separator },
                O::Sep { separator: &empty },
                O::Collection {
                    separator: &empty,
                    key_val_separator: Some(&empty)
                },
                O::Other,
            ]),
            [empty, separator, key_value]
        );
    }
}
