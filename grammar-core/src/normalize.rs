use crate::{
    derive_runtime_analysis, BuiltinToken, CategoryId, CollectionKind, EngineTables,
    ExactParseCost, GrammarCoreV1, ProductionId, RuntimeAnalysisError, RuntimeCollectionLayout,
    RuntimeRule, RuntimeRuleSemantic, RuntimeSymbol, SyntaxItem, TokenId, TokenPattern,
    ValidationError,
};
use std::collections::BTreeMap;

pub fn builtin_token_pattern(token: BuiltinToken) -> Option<&'static str> {
    match token {
        BuiltinToken::Identifier => Some(r"[\p{XID_Start}_][\p{XID_Continue}_]*"),
        BuiltinToken::Integer => Some(r"[0-9]+"),
        BuiltinToken::Float => Some(r"[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?|[0-9]+[eE][+-]?[0-9]+"),
        BuiltinToken::String => Some(r#""([^"\\]|\\.)*""#),
        BuiltinToken::Boolean => Some(r"true|false"),
        BuiltinToken::EndOfInput => None,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EngineNormalizationError {
    InvalidGrammar(Vec<ValidationError>),
    NonExactProfile,
    MissingIdentifierToken,
    MissingSeparatorToken(String),
    InvalidSyntaxShape(String),
    TooManySymbols,
    TooManyRules,
    TooManyNonterminals,
    TooManySemanticSlots,
    Analysis(RuntimeAnalysisError),
}

/// Canonically normalize semantic EBNF into the RTN/WPDA table layer.
///
/// This function is deliberately part of the stable grammar-core crate: both
/// compilers and parser-image admission use the same deterministic lowering,
/// so structurally valid cache data cannot substitute a different grammar.
pub fn normalize_runtime_engine(
    grammar: &GrammarCoreV1,
) -> Result<EngineTables, EngineNormalizationError> {
    grammar
        .validate()
        .map_err(EngineNormalizationError::InvalidGrammar)?;
    EngineNormalizer::new(grammar)?.normalize()
}

struct EngineNormalizer<'a> {
    grammar: &'a GrammarCoreV1,
    default_cost: ExactParseCost,
    next_nonterminal: u32,
    rules: Vec<PendingRule>,
    literals: BTreeMap<&'a str, TokenId>,
    identifier: Option<TokenId>,
}

struct PendingRule {
    lhs: u32,
    symbols: Vec<RuntimeSymbol>,
    production: Option<ProductionId>,
    semantic: RuntimeRuleSemantic,
    cost: ExactParseCost,
}

impl<'a> EngineNormalizer<'a> {
    fn new(grammar: &'a GrammarCoreV1) -> Result<Self, EngineNormalizationError> {
        let default_cost = grammar
            .weight_profile
            .exact_default()
            .ok_or(EngineNormalizationError::NonExactProfile)?;
        let next_nonterminal = u32::try_from(grammar.categories.len())
            .map_err(|_| EngineNormalizationError::TooManyNonterminals)?;
        let literals = grammar
            .tokens
            .iter()
            .filter_map(|token| match &token.pattern {
                TokenPattern::Literal(text) => Some((text.as_str(), token.id)),
                _ => None,
            })
            .collect();
        let identifier = grammar.tokens.iter().find_map(|token| {
            matches!(token.pattern, TokenPattern::Builtin(BuiltinToken::Identifier))
                .then_some(token.id)
        });
        Ok(Self {
            grammar,
            default_cost,
            next_nonterminal,
            rules: Vec::new(),
            literals,
            identifier,
        })
    }

    fn normalize(mut self) -> Result<EngineTables, EngineNormalizationError> {
        for production in &self.grammar.productions {
            let symbols = self.lower_items(&production.syntax)?;
            self.rules.push(PendingRule {
                lhs: production.result.0,
                symbols,
                production: Some(production.id),
                semantic: RuntimeRuleSemantic::Reduce,
                cost: self.default_cost,
            });
        }
        self.rules.sort_by_key(|rule| rule.lhs);
        let nonterminal_count = self.next_nonterminal;
        let mut runtime_rules = Vec::with_capacity(self.rules.len());
        let mut runtime_symbols = Vec::new();
        let mut nonterminal_rule_starts = Vec::with_capacity(nonterminal_count as usize + 1);
        let mut cursor = 0usize;
        for nonterminal in 0..nonterminal_count {
            nonterminal_rule_starts
                .push(u32::try_from(cursor).map_err(|_| EngineNormalizationError::TooManyRules)?);
            while cursor < self.rules.len() && self.rules[cursor].lhs == nonterminal {
                let pending = &self.rules[cursor];
                let symbol_start = u32::try_from(runtime_symbols.len())
                    .map_err(|_| EngineNormalizationError::TooManySymbols)?;
                runtime_symbols.extend(pending.symbols.iter().cloned());
                runtime_rules.push(RuntimeRule {
                    lhs: pending.lhs,
                    symbol_start,
                    symbol_len: u16::try_from(pending.symbols.len())
                        .map_err(|_| EngineNormalizationError::TooManySymbols)?,
                    production: pending.production,
                    semantic: pending.semantic,
                    cost: pending.cost,
                });
                cursor += 1;
            }
        }
        nonterminal_rule_starts.push(
            u32::try_from(runtime_rules.len())
                .map_err(|_| EngineNormalizationError::TooManyRules)?,
        );
        if cursor != self.rules.len() {
            return Err(EngineNormalizationError::TooManyNonterminals);
        }
        let start_nonterminals = {
            let primary: Vec<_> = self
                .grammar
                .categories
                .iter()
                .filter(|category| category.primary)
                .map(|category| category.id.0)
                .collect();
            if primary.is_empty() && !self.grammar.categories.is_empty() {
                vec![0]
            } else {
                primary
            }
        };
        let mut engine = EngineTables {
            nonterminal_count,
            start_nonterminals,
            nonterminal_rule_starts,
            runtime_rules,
            runtime_symbols,
            ..EngineTables::default()
        };
        let analysis =
            derive_runtime_analysis(&engine).map_err(EngineNormalizationError::Analysis)?;
        engine.same_span_ranks = analysis.same_span_ranks;
        engine.category_min_spans =
            analysis.nonterminal_min_spans[..self.grammar.categories.len()].to_vec();
        Ok(engine)
    }

    fn lower_items(
        &mut self,
        items: &[SyntaxItem],
    ) -> Result<Vec<RuntimeSymbol>, EngineNormalizationError> {
        enum Job<'b> {
            Items(&'b [SyntaxItem]),
            Item(&'b SyntaxItem),
            FinishItems(usize),
            FinishCollection {
                separator: &'b str,
                layout: RuntimeCollectionLayout,
                nonempty: bool,
            },
            FinishOptional {
                slots: u16,
            },
        }

        let mut jobs = vec![Job::Items(items)];
        let mut values: Vec<Vec<RuntimeSymbol>> = Vec::new();
        while let Some(job) = jobs.pop() {
            match job {
                Job::Items(items) => {
                    jobs.push(Job::FinishItems(items.len()));
                    for item in items.iter().rev() {
                        jobs.push(Job::Item(item));
                    }
                },
                Job::FinishItems(count) => {
                    let start = values
                        .len()
                        .checked_sub(count)
                        .expect("every syntax item result is scheduled");
                    let chunks = values.split_off(start);
                    let capacity = chunks.iter().map(Vec::len).sum();
                    let mut output = Vec::with_capacity(capacity);
                    for mut chunk in chunks {
                        output.append(&mut chunk);
                    }
                    values.push(output);
                },
                Job::Item(item) => match item {
                    SyntaxItem::Token(token) => {
                        values.push(vec![RuntimeSymbol::Token { token: *token, capture: false }]);
                    },
                    SyntaxItem::Category { category, .. } | SyntaxItem::Binder { category, .. } => {
                        values.push(vec![RuntimeSymbol::Nonterminal {
                            nonterminal: category.0,
                            capture: true,
                        }]);
                    },
                    SyntaxItem::CaptureIdent { .. } => {
                        let token = self
                            .identifier
                            .ok_or(EngineNormalizationError::MissingIdentifierToken)?;
                        values.push(vec![RuntimeSymbol::Token { token, capture: true }]);
                    },
                    SyntaxItem::CaptureToken { token, .. } => {
                        values.push(vec![RuntimeSymbol::Token { token: *token, capture: true }]);
                    },
                    SyntaxItem::Collection {
                        key,
                        element,
                        separator,
                        kind,
                        key_value_separator,
                        ..
                    } => {
                        let body = self.collection_element_symbols(
                            *key,
                            *element,
                            *kind,
                            key_value_separator.as_deref(),
                        )?;
                        let layout = RuntimeCollectionLayout::Uniform { slots: 1, kind: *kind };
                        let auxiliary = self.collection_aux(body, separator, layout, false)?;
                        values.push(vec![RuntimeSymbol::Nonterminal {
                            nonterminal: auxiliary,
                            capture: true,
                        }]);
                    },
                    SyntaxItem::Repeat { body, separator, kind } => {
                        let layout = RuntimeCollectionLayout::Uniform {
                            slots: slot_count(body)?,
                            kind: *kind,
                        };
                        jobs.push(Job::FinishCollection { separator, layout, nonempty: false });
                        jobs.push(Job::Items(body));
                    },
                    SyntaxItem::Sequence(body) => jobs.push(Job::Items(body)),
                    SyntaxItem::Optional(body) => {
                        jobs.push(Job::FinishOptional { slots: slot_count(body)? });
                        jobs.push(Job::Items(body));
                    },
                    SyntaxItem::Separated { source, separator } => match source.as_ref() {
                        SyntaxItem::Mapped { source, body, .. } => {
                            let layout = match source.as_ref() {
                                SyntaxItem::Collection { kind, .. } => {
                                    RuntimeCollectionLayout::Uniform { slots: 1, kind: *kind }
                                },
                                SyntaxItem::Binder { multiple: true, .. } => {
                                    RuntimeCollectionLayout::Uniform {
                                        slots: 1,
                                        kind: CollectionKind::List,
                                    }
                                },
                                SyntaxItem::Zip { left_kind, right_kind, .. } => {
                                    RuntimeCollectionLayout::Pair {
                                        left: *left_kind,
                                        right: *right_kind,
                                    }
                                },
                                _ => {
                                    return Err(EngineNormalizationError::InvalidSyntaxShape(
                                        "mapped source is not a collection or zip".into(),
                                    ))
                                },
                            };
                            jobs.push(Job::FinishCollection { separator, layout, nonempty: true });
                            jobs.push(Job::Items(body));
                        },
                        SyntaxItem::Collection {
                            key, element, kind, key_value_separator, ..
                        } => {
                            let body = self.collection_element_symbols(
                                *key,
                                *element,
                                *kind,
                                key_value_separator.as_deref(),
                            )?;
                            let layout = RuntimeCollectionLayout::Uniform { slots: 1, kind: *kind };
                            let auxiliary = self.collection_aux(body, separator, layout, true)?;
                            values.push(vec![RuntimeSymbol::Nonterminal {
                                nonterminal: auxiliary,
                                capture: true,
                            }]);
                        },
                        source => {
                            let layout = RuntimeCollectionLayout::Uniform {
                                slots: slot_count(std::slice::from_ref(source))?,
                                kind: CollectionKind::List,
                            };
                            jobs.push(Job::FinishCollection { separator, layout, nonempty: true });
                            jobs.push(Job::Item(source));
                        },
                    },
                    SyntaxItem::Mapped { .. } | SyntaxItem::Zip { .. } => {
                        return Err(EngineNormalizationError::InvalidSyntaxShape(
                            "map and zip are valid only as the source of separated syntax".into(),
                        ));
                    },
                    SyntaxItem::ForeignLanguage { open, close, .. } => {
                        values.push(vec![RuntimeSymbol::Foreign {
                            open: open.clone(),
                            close: close.clone(),
                            capture: true,
                        }]);
                    },
                    SyntaxItem::Guard { .. } => {
                        let auxiliary = self.new_nonterminal()?;
                        self.rules.push(PendingRule {
                            lhs: auxiliary,
                            symbols: Vec::new(),
                            production: None,
                            semantic: RuntimeRuleSemantic::Unit { slots: 1 },
                            cost: ExactParseCost::default(),
                        });
                        values.push(vec![RuntimeSymbol::Nonterminal {
                            nonterminal: auxiliary,
                            capture: true,
                        }]);
                    },
                },
                Job::FinishCollection { separator, layout, nonempty } => {
                    let body = values.pop().expect("a collection body result is scheduled");
                    let auxiliary = self.collection_aux(body, separator, layout, nonempty)?;
                    values.push(vec![RuntimeSymbol::Nonterminal {
                        nonterminal: auxiliary,
                        capture: true,
                    }]);
                },
                Job::FinishOptional { slots } => {
                    let body = values.pop().expect("an optional body result is scheduled");
                    let auxiliary = self.new_nonterminal()?;
                    self.rules.push(PendingRule {
                        lhs: auxiliary,
                        symbols: Vec::new(),
                        production: None,
                        semantic: RuntimeRuleSemantic::EmptyOptional { slots },
                        cost: ExactParseCost::default(),
                    });
                    self.rules.push(PendingRule {
                        lhs: auxiliary,
                        symbols: body,
                        production: None,
                        semantic: RuntimeRuleSemantic::PresentOptional { slots },
                        cost: ExactParseCost::default(),
                    });
                    values.push(vec![RuntimeSymbol::Nonterminal {
                        nonterminal: auxiliary,
                        capture: true,
                    }]);
                },
            }
        }
        if values.len() != 1 {
            return Err(EngineNormalizationError::InvalidSyntaxShape(
                "syntax lowering produced an invalid value stack".into(),
            ));
        }
        Ok(values.pop().expect("checked one syntax result"))
    }

    fn collection_element_symbols(
        &mut self,
        key: Option<CategoryId>,
        element: CategoryId,
        kind: CollectionKind,
        key_value_separator: Option<&str>,
    ) -> Result<Vec<RuntimeSymbol>, EngineNormalizationError> {
        if matches!(kind, CollectionKind::Map | CollectionKind::PathMap) {
            let key = key.ok_or_else(|| {
                EngineNormalizationError::InvalidSyntaxShape(
                    "map collection is missing its key category".into(),
                )
            })?;
            let separator = key_value_separator.ok_or_else(|| {
                EngineNormalizationError::InvalidSyntaxShape(
                    "map collection is missing its key/value separator".into(),
                )
            })?;
            let separator =
                self.literals.get(separator).copied().ok_or_else(|| {
                    EngineNormalizationError::MissingSeparatorToken(separator.into())
                })?;
            let tuple = self.new_nonterminal()?;
            self.rules.push(PendingRule {
                lhs: tuple,
                symbols: vec![
                    RuntimeSymbol::Nonterminal { nonterminal: key.0, capture: true },
                    RuntimeSymbol::Token { token: separator, capture: false },
                    RuntimeSymbol::Nonterminal { nonterminal: element.0, capture: true },
                ],
                production: None,
                semantic: RuntimeRuleSemantic::Tuple { slots: 2 },
                cost: ExactParseCost::default(),
            });
            Ok(vec![RuntimeSymbol::Nonterminal { nonterminal: tuple, capture: true }])
        } else {
            Ok(vec![RuntimeSymbol::Nonterminal { nonterminal: element.0, capture: true }])
        }
    }

    fn collection_aux(
        &mut self,
        body: Vec<RuntimeSymbol>,
        separator: &str,
        layout: RuntimeCollectionLayout,
        nonempty: bool,
    ) -> Result<u32, EngineNormalizationError> {
        let nonempty_auxiliary = self.new_nonterminal()?;
        self.rules.push(PendingRule {
            lhs: nonempty_auxiliary,
            symbols: body.clone(),
            production: None,
            semantic: RuntimeRuleSemantic::SingletonCollection { layout },
            cost: ExactParseCost::default(),
        });
        let mut append = vec![RuntimeSymbol::Nonterminal {
            nonterminal: nonempty_auxiliary,
            capture: true,
        }];
        if !separator.is_empty() {
            let token =
                self.literals.get(separator).copied().ok_or_else(|| {
                    EngineNormalizationError::MissingSeparatorToken(separator.into())
                })?;
            append.push(RuntimeSymbol::Token { token, capture: false });
        }
        append.extend(body);
        self.rules.push(PendingRule {
            lhs: nonempty_auxiliary,
            symbols: append,
            production: None,
            semantic: RuntimeRuleSemantic::AppendCollection { layout },
            cost: ExactParseCost::default(),
        });
        let collection_auxiliary = self.new_nonterminal()?;
        if !nonempty {
            self.rules.push(PendingRule {
                lhs: collection_auxiliary,
                symbols: Vec::new(),
                production: None,
                semantic: RuntimeRuleSemantic::EmptyCollection { layout },
                cost: ExactParseCost::default(),
            });
        }
        self.rules.push(PendingRule {
            lhs: collection_auxiliary,
            symbols: vec![RuntimeSymbol::Nonterminal {
                nonterminal: nonempty_auxiliary,
                capture: true,
            }],
            production: None,
            semantic: RuntimeRuleSemantic::FinalizeCollection { layout },
            cost: ExactParseCost::default(),
        });
        Ok(collection_auxiliary)
    }

    fn new_nonterminal(&mut self) -> Result<u32, EngineNormalizationError> {
        let result = self.next_nonterminal;
        self.next_nonterminal = self
            .next_nonterminal
            .checked_add(1)
            .ok_or(EngineNormalizationError::TooManyNonterminals)?;
        Ok(result)
    }
}

fn slot_count(items: &[SyntaxItem]) -> Result<u16, EngineNormalizationError> {
    let mut count = 0u16;
    let mut pending: Vec<_> = items.iter().collect();
    while let Some(item) = pending.pop() {
        match item {
            SyntaxItem::Token(_) => {},
            SyntaxItem::Category { .. }
            | SyntaxItem::CaptureIdent { .. }
            | SyntaxItem::CaptureToken { .. }
            | SyntaxItem::Binder { .. }
            | SyntaxItem::Collection { .. }
            | SyntaxItem::ForeignLanguage { .. }
            | SyntaxItem::Guard { .. } => {
                count = count
                    .checked_add(1)
                    .ok_or(EngineNormalizationError::TooManySemanticSlots)?;
            },
            SyntaxItem::Repeat { body, .. }
            | SyntaxItem::Sequence(body)
            | SyntaxItem::Optional(body) => pending.extend(body),
            SyntaxItem::Zip { .. } => {
                count = count
                    .checked_add(2)
                    .ok_or(EngineNormalizationError::TooManySemanticSlots)?;
            },
            SyntaxItem::Separated { source, .. } | SyntaxItem::Mapped { source, .. } => {
                pending.push(source);
            },
        }
    }
    Ok(count)
}
