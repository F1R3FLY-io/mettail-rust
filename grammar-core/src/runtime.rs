use crate::{
    runtime_capability_requirements, Associativity, CategoryId, DerivationRank, DynamicValue,
    ExactParseCost, GrammarCoreV1, ModeId, NativeEvaluation, ParserImageV1, ProductionId,
    RuntimeCapabilityBindings, RuntimeCapabilityError, RuntimeCapabilityKey,
    RuntimeCapabilityManifest, RuntimeRule, RuntimeRuleSemantic, RuntimeSymbol, SourceRuleRank,
    SourceSpan, TokenDecoder, TokenId, TokenPattern,
};
use rigail::Semiring;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WeightedParse {
    /// Recognition witness before native evaluation. Constructor and hole
    /// provenance lives here even when `value` is evaluated to a scalar.
    pub syntax: DynamicValue,
    /// Semantic value after the grammar's declared native evaluation.
    pub value: DynamicValue,
    /// Lawful scalar min-plus path cost. It carries no derivation provenance.
    pub cost: ExactParseCost,
    /// Canonical provenance used only to refine equal-cost output order.
    pub rank: DerivationRank,
    /// Root production witness. A template consisting solely of one admitted
    /// hole has no constructor production and therefore carries `None`.
    pub production: Option<ProductionId>,
}

/// One piece of a structural FLT input. Text pieces are lexed independently;
/// a hole is admitted as a category edge in the parser lattice and is never
/// rendered into text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeTemplatePiece {
    Text(String),
    Hole(u32),
}

/// Declaration for one stable FLT telescope entry. `category = None` requests
/// position-driven inference over categories that admit variables.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimeTemplateHole {
    pub id: u32,
    pub category: Option<CategoryId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeError {
    Image(String),
    InputTooLarge,
    Lex { byte: usize },
    LexerModeUnderflow { byte: usize },
    LexerModeUnclosed { byte: usize, depth: usize },
    LexerModeDepthLimit { byte: usize },
    ForeignNestingLimit { byte: usize },
    InvalidCategory(CategoryId),
    InvalidTokenValue { token: TokenId, text: String },
    MissingCapability(String),
    NativeSourceForbidden,
    ForeignLanguage { byte: usize, message: String },
    ParseItemLimit,
    ForestNodeLimit,
    ForestCycle,
    SemanticResultLimit,
    BadReduction(u32),
    Reduction(String),
    InvalidRuntimePolicy(&'static str),
    DynamicValueEncoding(String),
    InvalidTemplate(&'static str),
    InvalidTemplateHole { id: u32 },
    TemplateHoleCategoryConflict { id: u32 },
    TemplateCacheCycle,
    Capability(RuntimeCapabilityError),
    NoParse,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimePolicy {
    pub max_input_bytes: u32,
    pub max_parse_items: u32,
    pub max_forest_nodes: u32,
    pub max_semantic_results: u32,
    /// Maximum number of typed process-hole bindings in one FLT pattern.
    /// This is independent of parse-result cardinality.
    pub max_capture_bindings: u32,
    /// Maximum number of completed symbolic FLT parses retained per installed
    /// language. Zero disables memoization without disabling template parsing.
    pub max_symbolic_template_cache_entries: u32,
    /// Maximum retained logical heap weight of those symbolic parses. The
    /// cache also enforces the entry limit, so metadata remains bounded.
    pub max_symbolic_template_cache_weight: u64,
    pub max_lexer_mode_depth: u16,
    pub max_foreign_nesting: u16,
}

impl Default for RuntimePolicy {
    fn default() -> Self {
        Self {
            max_input_bytes: 16 * 1024 * 1024,
            max_parse_items: 10_000_000,
            max_forest_nodes: 10_000_000,
            max_semantic_results: 1_000_000,
            max_capture_bindings: 65_536,
            max_symbolic_template_cache_entries: 256,
            max_symbolic_template_cache_weight: 64 * 1024 * 1024,
            max_lexer_mode_depth: 1_024,
            max_foreign_nesting: 1_024,
        }
    }
}

#[derive(Clone, Copy)]
struct EffectiveRuntimeLimits {
    input_bytes: usize,
    parse_items: usize,
    forest_nodes: usize,
    semantic_results: usize,
    capture_bindings: usize,
    lexer_mode_depth: usize,
    foreign_nesting: u32,
}

/// Explicit host capabilities available to one runtime parser. Implementations
/// are shareable because installed-language system processes may execute parser
/// work on a bounded blocking worker rather than the async reducer thread.
pub trait RuntimeHost: Send + Sync {
    /// Identify a deterministic token-decoding/native-evaluation environment
    /// for symbolic-template memoization. Implementations must return the same
    /// value exactly while every [`RuntimeHost`] result is stable for equal
    /// inputs, and must change it before such behavior changes. Stateful or
    /// effectful hosts should retain the safe default of `None`.
    fn semantic_cache_commitment(&self) -> Option<[u8; 32]> {
        None
    }

    /// Return the exact immutable implementation manifest for one
    /// fingerprint-scoped callback. The installer and parser re-read it; a
    /// changing or revoked result fails closed.
    fn capability_manifest(
        &self,
        _key: &RuntimeCapabilityKey,
    ) -> Option<RuntimeCapabilityManifest> {
        None
    }

    fn decode_token(&self, capability: &str, text: &str) -> Result<DynamicValue, String> {
        let _ = text;
        Err(format!("unavailable token decoder capability `{capability}`"))
    }

    fn evaluate(
        &self,
        evaluation: &NativeEvaluation,
        inputs: &[DynamicValue],
        span: SourceSpan,
    ) -> Result<DynamicValue, String> {
        let _ = span;
        default_evaluate(evaluation, inputs)
    }

    fn parse_foreign(
        &self,
        open: &str,
        close: &str,
        source: &str,
        span: SourceSpan,
    ) -> Result<DynamicValue, String> {
        let _ = (open, close, source, span);
        Err("no foreign-language parser capability is installed".into())
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct DefaultRuntimeHost;

impl RuntimeHost for DefaultRuntimeHost {
    fn semantic_cache_commitment(&self) -> Option<[u8; 32]> {
        Some(*blake3::hash(b"mettail-default-runtime-host/1").as_bytes())
    }
}

pub struct RuntimeParser<'a> {
    grammar: &'a GrammarCoreV1,
    image: &'a ParserImageV1,
    host: &'a dyn RuntimeHost,
    capability_bindings: RuntimeCapabilityBindings,
    limits: EffectiveRuntimeLimits,
}

impl<'a> RuntimeParser<'a> {
    pub fn new(
        grammar: &'a GrammarCoreV1,
        image: &'a ParserImageV1,
        compiler_abi: &str,
        unicode_abi: &str,
        host: &'a dyn RuntimeHost,
    ) -> Result<Self, RuntimeError> {
        Self::new_with_policy(
            grammar,
            image,
            compiler_abi,
            unicode_abi,
            host,
            RuntimePolicy::default(),
        )
    }

    pub fn new_with_policy(
        grammar: &'a GrammarCoreV1,
        image: &'a ParserImageV1,
        compiler_abi: &str,
        unicode_abi: &str,
        host: &'a dyn RuntimeHost,
        policy: RuntimePolicy,
    ) -> Result<Self, RuntimeError> {
        image
            .verify_executable(grammar, compiler_abi, unicode_abi)
            .map_err(|error| RuntimeError::Image(format!("{error:?}")))?;
        let requirements = runtime_capability_requirements(grammar, image.core_fingerprint)
            .map_err(RuntimeError::Capability)?;
        let bindings =
            RuntimeCapabilityBindings::bind(&requirements, |key| host.capability_manifest(key))
                .map_err(RuntimeError::Capability)?;
        Self::new_with_policy_and_bindings(
            grammar,
            image,
            compiler_abi,
            unicode_abi,
            host,
            policy,
            bindings,
        )
    }

    pub(crate) fn new_with_policy_and_bindings(
        grammar: &'a GrammarCoreV1,
        image: &'a ParserImageV1,
        compiler_abi: &str,
        unicode_abi: &str,
        host: &'a dyn RuntimeHost,
        policy: RuntimePolicy,
        capability_bindings: RuntimeCapabilityBindings,
    ) -> Result<Self, RuntimeError> {
        if policy.max_lexer_mode_depth == 0 {
            return Err(RuntimeError::InvalidRuntimePolicy(
                "max_lexer_mode_depth must be positive",
            ));
        }
        if policy.max_foreign_nesting == 0 {
            return Err(RuntimeError::InvalidRuntimePolicy("max_foreign_nesting must be positive"));
        }
        image
            .verify_executable(grammar, compiler_abi, unicode_abi)
            .map_err(|error| RuntimeError::Image(format!("{error:?}")))?;
        Ok(Self {
            grammar,
            image,
            host,
            capability_bindings,
            limits: EffectiveRuntimeLimits {
                input_bytes: grammar.limits.max_input_bytes.min(policy.max_input_bytes) as usize,
                parse_items: grammar.limits.max_parse_items.min(policy.max_parse_items) as usize,
                forest_nodes: grammar.limits.max_forest_nodes.min(policy.max_forest_nodes) as usize,
                semantic_results: grammar
                    .limits
                    .max_semantic_results
                    .min(policy.max_semantic_results) as usize,
                capture_bindings: policy.max_capture_bindings as usize,
                lexer_mode_depth: policy.max_lexer_mode_depth as usize,
                foreign_nesting: u32::from(policy.max_foreign_nesting),
            },
        })
    }

    pub fn parse(&self, source: &str) -> Result<Vec<WeightedParse>, RuntimeError> {
        self.parse_categories(source, &self.image.engine.start_nonterminals)
    }

    pub fn parse_category(
        &self,
        source: &str,
        category: CategoryId,
    ) -> Result<Vec<WeightedParse>, RuntimeError> {
        if category.0 as usize >= self.grammar.categories.len() {
            return Err(RuntimeError::InvalidCategory(category));
        }
        self.parse_categories(source, &[category.0])
    }

    /// Parse an FLT template without rendering holes into guest source.
    ///
    /// Every text piece is lexed as an independent fragment while lexer-mode
    /// state is carried between fragments. Hole pieces become category-labelled
    /// edges of width one in the logical token lattice. Untyped repeated holes
    /// are retained only when every occurrence is inferred at the same category.
    pub fn parse_template(
        &self,
        pieces: &[RuntimeTemplatePiece],
        holes: &[RuntimeTemplateHole],
        category: Option<CategoryId>,
    ) -> Result<Vec<WeightedParse>, RuntimeError> {
        if let Some(category) = category {
            if category.0 as usize >= self.grammar.categories.len() {
                return Err(RuntimeError::InvalidCategory(category));
            }
        }
        let input = self.lex_template(pieces, holes)?;
        let categories = category
            .map(|category| vec![category.0])
            .unwrap_or_else(|| self.image.engine.start_nonterminals.clone());
        let mut forest = ForestBuilder::new_template(self, input);
        let roots = forest.recognize(&categories)?;
        let output = forest.realize_weighted(roots)?;
        let mut conflict = None;
        let consistent =
            output.into_iter().filter(|result| {
                match validate_template_hole_categories(&result.syntax, holes) {
                    Ok(()) => true,
                    Err(id) => {
                        conflict.get_or_insert(id);
                        false
                    },
                }
            });
        match normalize_weighted_output(consistent) {
            Err(RuntimeError::NoParse) if conflict.is_some() => {
                Err(RuntimeError::TemplateHoleCategoryConflict { id: conflict.expect("checked") })
            },
            result => result,
        }
    }

    fn parse_categories(
        &self,
        source: &str,
        categories: &[u32],
    ) -> Result<Vec<WeightedParse>, RuntimeError> {
        if source.len() > self.limits.input_bytes {
            return Err(RuntimeError::InputTooLarge);
        }
        let lexemes = self.lex(source)?;
        let mut forest = ForestBuilder::new(self, source, lexemes);
        let roots = forest.recognize(categories)?;
        normalize_weighted_output(forest.realize_weighted(roots)?.into_iter())
    }

    fn lex_template<'template>(
        &self,
        pieces: &'template [RuntimeTemplatePiece],
        holes: &[RuntimeTemplateHole],
    ) -> Result<TemplateLexing<'template>, RuntimeError> {
        // Each canonical piece consumes at least one byte or one structural
        // lattice position. Bound the work before allocating occurrence state;
        // callers of this neutral API need not originate from an FltNode.
        if pieces.len() > self.limits.input_bytes {
            return Err(RuntimeError::InputTooLarge);
        }
        if holes.len() > self.limits.capture_bindings {
            return Err(RuntimeError::InvalidTemplate("hole declaration limit exceeded"));
        }
        if holes
            .iter()
            .enumerate()
            .any(|(index, hole)| hole.id as usize != index)
        {
            return Err(RuntimeError::InvalidTemplate("hole declarations must have dense ids"));
        }
        for hole in holes {
            if let Some(category) = hole.category {
                let Some(definition) = self.grammar.categories.get(category.0 as usize) else {
                    return Err(RuntimeError::InvalidCategory(category));
                };
                if !definition.admits_variables {
                    return Err(RuntimeError::InvalidTemplateHole { id: hole.id });
                }
            }
        }

        let mut mode_stack = vec![ModeId(0)];
        let mut output = BTreeMap::new();
        let mut fragments = BTreeMap::new();
        let mut occurrences = vec![0usize; holes.len()];
        let mut lattice_holes = BTreeMap::new();
        let mut position = 0usize;
        let foreign_delimiters = self.foreign_delimiters();

        for piece in pieces {
            match piece {
                RuntimeTemplatePiece::Hole(id) => {
                    let declaration = holes
                        .get(*id as usize)
                        .filter(|hole| hole.id == *id)
                        .ok_or(RuntimeError::InvalidTemplateHole { id: *id })?;
                    occurrences[*id as usize] += 1;
                    lattice_holes.insert(
                        position,
                        TemplateHoleOccurrence {
                            id: *id,
                            category: declaration.category,
                            end: position.checked_add(1).ok_or(RuntimeError::InputTooLarge)?,
                        },
                    );
                    position = position.checked_add(1).ok_or(RuntimeError::InputTooLarge)?;
                },
                RuntimeTemplatePiece::Text(fragment) => {
                    if fragment.is_empty() {
                        return Err(RuntimeError::InvalidTemplate("text pieces must be nonempty"));
                    }
                    let fragment_start = position;
                    fragments.insert(fragment_start, fragment.as_str());
                    let bytes = fragment.as_bytes();
                    let mut local = 0usize;
                    while local < bytes.len() {
                        if let Some((open, close)) = foreign_delimiters
                            .iter()
                            .copied()
                            .find(|(open, _)| fragment[local..].starts_with(open))
                        {
                            let end = match delimited_span(
                                fragment,
                                local,
                                open,
                                close,
                                self.limits.foreign_nesting,
                            ) {
                                Ok(Some((_, _, end))) => end,
                                Ok(None) | Err(DelimitedSpanError::Unterminated) => {
                                    return Err(RuntimeError::ForeignLanguage {
                                        byte: fragment_start + local,
                                        message: format!(
                                            "unterminated foreign-language region `{open}` ... `{close}`"
                                        ),
                                    });
                                },
                                Err(DelimitedSpanError::NestingLimit) => {
                                    return Err(RuntimeError::ForeignNestingLimit {
                                        byte: fragment_start + local,
                                    });
                                },
                            };
                            local = end;
                            continue;
                        }

                        let mode = *mode_stack.last().expect("mode stack starts nonempty");
                        let mut state = *self
                            .image
                            .lexer
                            .mode_starts
                            .get(mode.0 as usize)
                            .ok_or(RuntimeError::Lex { byte: fragment_start + local })?;
                        let token_start = local;
                        let mut cursor = local;
                        let mut accepted: Option<(usize, Vec<TokenId>)> = None;
                        while cursor < bytes.len() {
                            let Some(next) =
                                lexer_transition(&self.image.lexer, state, bytes[cursor])
                            else {
                                break;
                            };
                            state = next;
                            cursor += 1;
                            let candidates = &self.image.lexer.states[state as usize].accept;
                            if !candidates.is_empty() {
                                accepted = Some((cursor, candidates.clone()));
                            }
                        }
                        let Some((end, mut candidates)) = accepted else {
                            return Err(RuntimeError::Lex { byte: fragment_start + token_start });
                        };
                        let primary = self.grammar.tokens[candidates[0].0 as usize].clone();
                        candidates.retain(|candidate| {
                            let token = &self.grammar.tokens[candidate.0 as usize];
                            token.transition == primary.transition
                                && token.channel == primary.channel
                        });
                        if primary.transition.pop {
                            if mode_stack.len() == 1 {
                                return Err(RuntimeError::LexerModeUnderflow {
                                    byte: fragment_start + token_start,
                                });
                            }
                            mode_stack.pop();
                        }
                        if let Some(push) = primary.transition.push {
                            if mode_stack.len() >= self.limits.lexer_mode_depth {
                                return Err(RuntimeError::LexerModeDepthLimit {
                                    byte: fragment_start + token_start,
                                });
                            }
                            mode_stack.push(push);
                        }
                        output.insert(
                            fragment_start + token_start,
                            Lexeme {
                                start: fragment_start + token_start,
                                end: fragment_start + end,
                                candidates,
                                hidden: primary.channel != "main",
                            },
                        );
                        local = end;
                    }
                    position = position
                        .checked_add(fragment.len())
                        .ok_or(RuntimeError::InputTooLarge)?;
                },
            }
            if position > self.limits.input_bytes {
                return Err(RuntimeError::InputTooLarge);
            }
        }

        if occurrences.contains(&0) {
            return Err(RuntimeError::InvalidTemplate("every declared hole must occur"));
        }
        if mode_stack.len() != 1 {
            return Err(RuntimeError::LexerModeUnclosed {
                byte: position,
                depth: mode_stack.len(),
            });
        }
        let mode = *mode_stack.last().expect("mode stack remains nonempty");
        let mut eof = self.grammar.modes[mode.0 as usize]
            .token_ids
            .iter()
            .copied()
            .filter(|token| {
                matches!(
                    self.grammar.tokens[token.0 as usize].pattern,
                    TokenPattern::Builtin(crate::BuiltinToken::EndOfInput)
                )
            })
            .collect::<Vec<_>>();
        eof.sort_by_key(|id| {
            let token = &self.grammar.tokens[id.0 as usize];
            (std::cmp::Reverse(token.priority), token.id)
        });
        if !eof.is_empty() {
            output.insert(
                position,
                Lexeme {
                    start: position,
                    end: position + 1,
                    candidates: eof,
                    hidden: false,
                },
            );
        }
        Ok(TemplateLexing {
            lexemes: output,
            fragments,
            holes: lattice_holes,
            end: position,
        })
    }

    fn foreign_delimiters(&self) -> Vec<(&str, &str)> {
        let mut delimiters = self
            .image
            .engine
            .runtime_symbols
            .iter()
            .filter_map(|symbol| match symbol {
                RuntimeSymbol::Foreign { open, close, .. } => Some((open.as_str(), close.as_str())),
                _ => None,
            })
            .collect::<Vec<_>>();
        delimiters.sort_unstable_by(|left, right| {
            right
                .0
                .len()
                .cmp(&left.0.len())
                .then_with(|| left.cmp(right))
        });
        delimiters.dedup();
        delimiters
    }

    fn lex(&self, source: &str) -> Result<BTreeMap<usize, Lexeme>, RuntimeError> {
        let bytes = source.as_bytes();
        let mut position = 0usize;
        let mut mode_stack = vec![ModeId(0)];
        let mut output = BTreeMap::new();
        let foreign_delimiters = self.foreign_delimiters();
        while position < bytes.len() {
            if let Some((open, close)) = foreign_delimiters
                .iter()
                .copied()
                .find(|(open, _)| source[position..].starts_with(open))
            {
                let end = match delimited_span(
                    source,
                    position,
                    open,
                    close,
                    self.limits.foreign_nesting,
                ) {
                    Ok(Some((_, _, end))) => end,
                    Ok(None) | Err(DelimitedSpanError::Unterminated) => {
                        return Err(RuntimeError::ForeignLanguage {
                            byte: position,
                            message: format!(
                                "unterminated foreign-language region `{open}` ... `{close}`"
                            ),
                        });
                    },
                    Err(DelimitedSpanError::NestingLimit) => {
                        return Err(RuntimeError::ForeignNestingLimit { byte: position });
                    },
                };
                position = end;
                continue;
            }
            let mode = *mode_stack.last().expect("mode stack starts nonempty");
            let mut state = *self
                .image
                .lexer
                .mode_starts
                .get(mode.0 as usize)
                .ok_or(RuntimeError::Lex { byte: position })?;
            let mut cursor = position;
            let mut accepted: Option<(usize, Vec<TokenId>)> = None;
            while cursor < bytes.len() {
                let Some(next) = lexer_transition(&self.image.lexer, state, bytes[cursor]) else {
                    break;
                };
                state = next;
                cursor += 1;
                let candidates = &self.image.lexer.states[state as usize].accept;
                if !candidates.is_empty() {
                    accepted = Some((cursor, candidates.clone()));
                }
            }
            let Some((end, mut candidates)) = accepted else {
                return Err(RuntimeError::Lex { byte: position });
            };
            let primary = self.grammar.tokens[candidates[0].0 as usize].clone();
            candidates.retain(|candidate| {
                let token = &self.grammar.tokens[candidate.0 as usize];
                token.transition == primary.transition && token.channel == primary.channel
            });
            if primary.transition.pop {
                if mode_stack.len() == 1 {
                    return Err(RuntimeError::LexerModeUnderflow { byte: position });
                }
                mode_stack.pop();
            }
            if let Some(push) = primary.transition.push {
                if mode_stack.len() >= self.limits.lexer_mode_depth {
                    return Err(RuntimeError::LexerModeDepthLimit { byte: position });
                }
                mode_stack.push(push);
            }
            output.insert(
                position,
                Lexeme {
                    start: position,
                    end,
                    candidates,
                    hidden: primary.channel != "main",
                },
            );
            position = end;
        }
        if mode_stack.len() != 1 {
            return Err(RuntimeError::LexerModeUnclosed {
                byte: position,
                depth: mode_stack.len(),
            });
        }
        let mode = *mode_stack.last().expect("mode stack remains nonempty");
        let mut eof = self.grammar.modes[mode.0 as usize]
            .token_ids
            .iter()
            .copied()
            .filter(|token| {
                matches!(
                    self.grammar.tokens[token.0 as usize].pattern,
                    TokenPattern::Builtin(crate::BuiltinToken::EndOfInput)
                )
            })
            .collect::<Vec<_>>();
        eof.sort_by_key(|id| {
            let token = &self.grammar.tokens[id.0 as usize];
            (std::cmp::Reverse(token.priority), token.id)
        });
        if !eof.is_empty() {
            output.insert(
                position,
                Lexeme {
                    start: position,
                    end: position + 1,
                    candidates: eof,
                    hidden: false,
                },
            );
        }
        Ok(output)
    }

    fn decode_token(&self, token: TokenId, text: &str) -> Result<DynamicValue, RuntimeError> {
        let definition = &self.grammar.tokens[token.0 as usize];
        let decoded = match &definition.decoder {
            TokenDecoder::Text => DynamicValue::Text(text.into()),
            TokenDecoder::Integer { radix } => decode_integer(text, radix.unwrap_or(10))
                .map(DynamicValue::Integer)
                .ok_or_else(|| RuntimeError::InvalidTokenValue { token, text: text.into() })?,
            TokenDecoder::Boolean { true_text, false_text } => {
                if text == true_text {
                    DynamicValue::Boolean(true)
                } else if text == false_text {
                    DynamicValue::Boolean(false)
                } else {
                    return Err(RuntimeError::InvalidTokenValue { token, text: text.into() });
                }
            },
            TokenDecoder::BytesHex => DynamicValue::Bytes(
                decode_hex(text)
                    .ok_or_else(|| RuntimeError::InvalidTokenValue { token, text: text.into() })?,
            ),
            TokenDecoder::Unit => DynamicValue::Unit,
            TokenDecoder::Capability(capability) => {
                let key = RuntimeCapabilityKey::token_decoder(
                    self.image.core_fingerprint,
                    capability.clone(),
                );
                let manifest = self.authorize_capability(&key, text.len(), 0)?;
                let result = self.host.decode_token(capability, text);
                self.revalidate_capability(&key, &manifest)?;
                result.map_err(RuntimeError::MissingCapability)?
            },
        };
        if let Some(evaluation) = &definition.evaluation {
            self.evaluate_native(evaluation, std::slice::from_ref(&decoded), SourceSpan::default())
        } else {
            Ok(decoded)
        }
    }

    fn evaluate_native(
        &self,
        evaluation: &NativeEvaluation,
        inputs: &[DynamicValue],
        span: SourceSpan,
    ) -> Result<DynamicValue, RuntimeError> {
        let NativeEvaluation::Handler(capability) = evaluation else {
            return match evaluation {
                NativeEvaluation::Operator(_) | NativeEvaluation::Carrier { .. } => {
                    default_evaluate(evaluation, inputs).map_err(RuntimeError::Reduction)
                },
                NativeEvaluation::Source { .. } => Err(RuntimeError::NativeSourceForbidden),
                NativeEvaluation::Handler(_) => unreachable!("matched above"),
            };
        };
        let key =
            RuntimeCapabilityKey::native_evaluator(self.image.core_fingerprint, capability.clone());
        let manifest = self.authorize_capability(&key, 0, inputs.len())?;
        let result = self.host.evaluate(evaluation, inputs, span);
        self.revalidate_capability(&key, &manifest)?;
        result.map_err(RuntimeError::Reduction)
    }

    fn parse_foreign_committed(
        &self,
        open: &str,
        close: &str,
        source: &str,
        span: SourceSpan,
    ) -> Result<DynamicValue, String> {
        let key = RuntimeCapabilityKey::foreign_bridge(self.image.core_fingerprint, open, close);
        let manifest = self
            .authorize_capability(&key, source.len(), 0)
            .map_err(|error| format!("{error:?}"))?;
        let result = self.host.parse_foreign(open, close, source, span);
        self.revalidate_capability(&key, &manifest)
            .map_err(|error| format!("{error:?}"))?;
        result
    }

    fn authorize_capability(
        &self,
        key: &RuntimeCapabilityKey,
        input_bytes: usize,
        values: usize,
    ) -> Result<RuntimeCapabilityManifest, RuntimeError> {
        let committed = self.capability_bindings.get(key).ok_or_else(|| {
            RuntimeError::Capability(RuntimeCapabilityError::Missing(Box::new(key.clone())))
        })?;
        let current = self.host.capability_manifest(key).ok_or_else(|| {
            RuntimeError::Capability(RuntimeCapabilityError::Changed(Box::new(key.clone())))
        })?;
        if current != *committed {
            return Err(RuntimeError::Capability(RuntimeCapabilityError::Changed(Box::new(
                key.clone(),
            ))));
        }
        if committed.cost.charge(input_bytes, values).is_none() {
            return Err(RuntimeError::Capability(RuntimeCapabilityError::CostExceeded(Box::new(
                key.clone(),
            ))));
        }
        Ok(committed.clone())
    }

    fn revalidate_capability(
        &self,
        key: &RuntimeCapabilityKey,
        committed: &RuntimeCapabilityManifest,
    ) -> Result<(), RuntimeError> {
        let current = self.host.capability_manifest(key).ok_or_else(|| {
            RuntimeError::Capability(RuntimeCapabilityError::Changed(Box::new(key.clone())))
        })?;
        if current != *committed {
            return Err(RuntimeError::Capability(RuntimeCapabilityError::Changed(Box::new(
                key.clone(),
            ))));
        }
        Ok(())
    }
}

fn normalize_weighted_output(
    output: impl Iterator<Item = WeightedParse>,
) -> Result<Vec<WeightedParse>, RuntimeError> {
    let mut keyed = output
        .map(|result| {
            let value_key = result
                .value
                .semantic_key()
                .map_err(|error| RuntimeError::DynamicValueEncoding(error.to_string()))?;
            let syntax_key = result
                .syntax
                .semantic_key()
                .map_err(|error| RuntimeError::DynamicValueEncoding(error.to_string()))?;
            Ok((
                result.cost,
                result.rank.clone(),
                result.production,
                syntax_key,
                value_key,
                result,
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;
    keyed.sort_by(|left, right| {
        (&left.0, &left.1, &left.2, &left.3, &left.4)
            .cmp(&(&right.0, &right.1, &right.2, &right.3, &right.4))
    });
    keyed.dedup_by(|left, right| {
        left.0 == right.0
            && left.1 == right.1
            && left.2 == right.2
            && left.3 == right.3
            && left.4 == right.4
    });
    let output = keyed
        .into_iter()
        .map(|(_, _, _, _, _, result)| result)
        .collect::<Vec<_>>();
    if output.is_empty() {
        Err(RuntimeError::NoParse)
    } else {
        Ok(output)
    }
}

fn validate_template_hole_categories(
    value: &DynamicValue,
    holes: &[RuntimeTemplateHole],
) -> Result<(), u32> {
    let mut inferred = vec![None; holes.len()];
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        match value {
            DynamicValue::Term(term) => pending.extend(term.fields.iter()),
            DynamicValue::TemplateHole { id, category } => {
                let declaration = holes
                    .get(*id as usize)
                    .filter(|declaration| declaration.id == *id)
                    .ok_or(*id)?;
                if declaration
                    .category
                    .is_some_and(|expected| expected != *category)
                {
                    return Err(*id);
                }
                match inferred[*id as usize] {
                    Some(previous) if previous != *category => return Err(*id),
                    Some(_) => {},
                    None => inferred[*id as usize] = Some(*category),
                }
            },
            DynamicValue::Sequence(values) => pending.extend(values.iter()),
            DynamicValue::Collection { entries, .. } => pending.extend(entries.iter()),
            DynamicValue::Text(_)
            | DynamicValue::Integer(_)
            | DynamicValue::Boolean(_)
            | DynamicValue::Bytes(_)
            | DynamicValue::Unit => {},
        }
    }
    inferred
        .iter()
        .enumerate()
        .find(|(_, category)| category.is_none())
        .map_or(Ok(()), |(id, _)| Err(id as u32))
}

fn lexer_transition(lexer: &crate::LexerImage, state: u32, byte: u8) -> Option<u32> {
    let state = lexer.states.get(state as usize)?;
    let start = state.transition_start as usize;
    let end = start + state.transition_len as usize;
    let transitions = &lexer.transitions[start..end];
    transitions
        .binary_search_by(|transition| {
            if byte < transition.start {
                std::cmp::Ordering::Greater
            } else if byte > transition.end {
                std::cmp::Ordering::Less
            } else {
                std::cmp::Ordering::Equal
            }
        })
        .ok()
        .map(|index| transitions[index].target)
}

#[derive(Clone)]
struct Lexeme {
    start: usize,
    end: usize,
    candidates: Vec<TokenId>,
    hidden: bool,
}

#[derive(Clone, Copy)]
struct TemplateHoleOccurrence {
    id: u32,
    category: Option<CategoryId>,
    end: usize,
}

struct TemplateLexing<'a> {
    lexemes: BTreeMap<usize, Lexeme>,
    fragments: BTreeMap<usize, &'a str>,
    holes: BTreeMap<usize, TemplateHoleOccurrence>,
    end: usize,
}

struct InputText<'a> {
    fragments: BTreeMap<usize, &'a str>,
    end: usize,
}

impl<'a> InputText<'a> {
    fn source(source: &'a str) -> Self {
        Self {
            fragments: BTreeMap::from([(0, source)]),
            end: source.len(),
        }
    }

    fn slice(&self, start: usize, end: usize) -> Option<&'a str> {
        if start == self.end && end == self.end.saturating_add(1) {
            return Some("");
        }
        let (base, fragment) = self.fragments.range(..=start).next_back()?;
        let local_start = start.checked_sub(*base)?;
        let local_end = end.checked_sub(*base)?;
        fragment.get(local_start..local_end)
    }

    fn delimited_span(
        &self,
        position: usize,
        open: &str,
        close: &str,
        max_nesting: u32,
    ) -> Result<Option<(usize, usize, usize)>, DelimitedSpanError> {
        let Some((base, fragment)) = self.fragments.range(..=position).next_back() else {
            return Ok(None);
        };
        let Some(local) = position.checked_sub(*base) else {
            return Ok(None);
        };
        delimited_span(fragment, local, open, close, max_nesting).map(|span| {
            span.map(|(content_start, content_end, end)| {
                (*base + content_start, *base + content_end, *base + end)
            })
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ItemKey {
    rule: u32,
    dot: u16,
    origin: usize,
    end: usize,
}

type NodeId = u32;

#[derive(Clone)]
enum ForestNode {
    Terminal {
        token: TokenId,
        start: usize,
        end: usize,
        alternative: u32,
    },
    Foreign {
        open: String,
        close: String,
        start: usize,
        content_start: usize,
        content_end: usize,
        end: usize,
    },
    Intermediate {
        item: ItemKey,
        alternatives: Vec<PackedPair>,
    },
    Nonterminal {
        start: usize,
        end: usize,
        alternatives: Vec<CompletedRule>,
        template_hole: Option<(u32, CategoryId)>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PackedPair {
    previous: Option<NodeId>,
    child: NodeId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CompletedRule {
    rule: u32,
    prefix: Option<NodeId>,
}

struct ForestBuilder<'a, 'b> {
    parser: &'a RuntimeParser<'b>,
    input: InputText<'a>,
    holes: BTreeMap<usize, TemplateHoleOccurrence>,
    lexemes: BTreeMap<usize, Lexeme>,
    items: HashSet<ItemKey>,
    queue: VecDeque<ItemKey>,
    waiting: HashMap<(usize, u32), Vec<ItemKey>>,
    completed: HashMap<(u32, usize), Vec<NodeId>>,
    nodes: Vec<ForestNode>,
    intermediate: HashMap<ItemKey, NodeId>,
    nonterminals: HashMap<(u32, usize, usize), NodeId>,
    hole_nonterminals: HashSet<(u32, usize, usize)>,
    terminals: HashMap<(TokenId, usize, usize), NodeId>,
    foreign: HashMap<(String, String, usize, usize), NodeId>,
}

struct RealizationContext {
    active: BTreeSet<NodeId>,
    memo: BTreeMap<NodeId, Vec<SemanticPath>>,
    remaining_results: usize,
}

impl RealizationContext {
    fn new(remaining_results: usize) -> Self {
        Self {
            active: BTreeSet::new(),
            memo: BTreeMap::new(),
            remaining_results,
        }
    }
}

impl<'a, 'b> ForestBuilder<'a, 'b> {
    fn new(
        parser: &'a RuntimeParser<'b>,
        source: &'a str,
        lexemes: BTreeMap<usize, Lexeme>,
    ) -> Self {
        Self {
            parser,
            input: InputText::source(source),
            holes: BTreeMap::new(),
            lexemes,
            items: HashSet::new(),
            queue: VecDeque::new(),
            waiting: HashMap::new(),
            completed: HashMap::new(),
            nodes: Vec::new(),
            intermediate: HashMap::new(),
            nonterminals: HashMap::new(),
            hole_nonterminals: HashSet::new(),
            terminals: HashMap::new(),
            foreign: HashMap::new(),
        }
    }

    fn new_template(parser: &'a RuntimeParser<'b>, input: TemplateLexing<'a>) -> Self {
        Self {
            parser,
            input: InputText {
                fragments: input.fragments,
                end: input.end,
            },
            holes: input.holes,
            lexemes: input.lexemes,
            items: HashSet::new(),
            queue: VecDeque::new(),
            waiting: HashMap::new(),
            completed: HashMap::new(),
            nodes: Vec::new(),
            intermediate: HashMap::new(),
            nonterminals: HashMap::new(),
            hole_nonterminals: HashSet::new(),
            terminals: HashMap::new(),
            foreign: HashMap::new(),
        }
    }

    fn recognize(&mut self, categories: &[u32]) -> Result<Vec<NodeId>, RuntimeError> {
        let start = self.canonical_position(0);
        for category in categories {
            self.complete_template_hole(*category, start)?;
            self.predict(*category, start)?;
        }
        while let Some(item) = self.queue.pop_front() {
            let rule = self.parser.image.engine.runtime_rules[item.rule as usize].clone();
            if item.dot as usize == rule.symbol_len as usize {
                let prefix = if item.dot == 0 {
                    None
                } else {
                    self.intermediate.get(&item).copied()
                };
                self.complete(rule.lhs, item.origin, item.end, item.rule, prefix)?;
                continue;
            }
            let symbol = self.parser.image.engine.runtime_symbols
                [(rule.symbol_start + u32::from(item.dot)) as usize]
                .clone();
            match symbol {
                RuntimeSymbol::Token { token, .. } => self.scan_token(item, token)?,
                RuntimeSymbol::Nonterminal { nonterminal, .. } => {
                    let key = (item.end, nonterminal);
                    if !self.waiting.entry(key).or_default().contains(&item) {
                        self.waiting.entry(key).or_default().push(item);
                    }
                    self.complete_template_hole(nonterminal, item.end)?;
                    self.predict(nonterminal, item.end)?;
                    for completed in self
                        .completed
                        .get(&(nonterminal, item.end))
                        .cloned()
                        .unwrap_or_default()
                    {
                        let end = match &self.nodes[completed as usize] {
                            ForestNode::Nonterminal { end, .. } => *end,
                            _ => unreachable!(),
                        };
                        self.advance(item, completed, end)?;
                    }
                },
                RuntimeSymbol::Foreign { open, close, .. } => {
                    self.scan_foreign(item, &open, &close)?;
                },
            }
        }
        let end = self.canonical_position(self.input.end);
        let eof_end = self.lexemes.get(&self.input.end).map(|lexeme| lexeme.end);
        let mut roots = Vec::new();
        for category in categories {
            for node in self
                .completed
                .get(&(*category, start))
                .into_iter()
                .flatten()
            {
                let node_end = match &self.nodes[*node as usize] {
                    ForestNode::Nonterminal { end, .. } => *end,
                    _ => unreachable!(),
                };
                if node_end == end || Some(node_end) == eof_end {
                    roots.push(*node);
                }
            }
        }
        roots.sort_unstable();
        roots.dedup();
        if roots.is_empty() {
            Err(RuntimeError::NoParse)
        } else {
            Ok(roots)
        }
    }

    fn predict(&mut self, nonterminal: u32, position: usize) -> Result<(), RuntimeError> {
        let start = self.parser.image.engine.nonterminal_rule_starts[nonterminal as usize];
        let end = self.parser.image.engine.nonterminal_rule_starts[nonterminal as usize + 1];
        for rule in start..end {
            self.add_item(
                ItemKey {
                    rule,
                    dot: 0,
                    origin: position,
                    end: position,
                },
                None,
            )?;
        }
        Ok(())
    }

    fn scan_token(&mut self, item: ItemKey, token: TokenId) -> Result<(), RuntimeError> {
        let position = self.canonical_position(item.end);
        let Some(lexeme) = self.lexemes.get(&position).cloned() else {
            return Ok(());
        };
        if !lexeme.candidates.contains(&token) {
            return Ok(());
        }
        let alternative = u32::try_from(
            lexeme
                .candidates
                .iter()
                .position(|candidate| *candidate == token)
                .expect("candidate membership checked above"),
        )
        .map_err(|_| RuntimeError::Image("lexer alternative ordinal exceeds u32".into()))?;
        let key = (token, lexeme.start, lexeme.end);
        let terminal = if let Some(node) = self.terminals.get(&key) {
            *node
        } else {
            let node = self.push_node(ForestNode::Terminal {
                token,
                start: lexeme.start,
                end: lexeme.end,
                alternative,
            })?;
            self.terminals.insert(key, node);
            node
        };
        let end = self.canonical_position(lexeme.end);
        self.advance(item, terminal, end)
    }

    fn scan_foreign(&mut self, item: ItemKey, open: &str, close: &str) -> Result<(), RuntimeError> {
        let position = self.canonical_position(item.end);
        let (content_start, content_end, end) = match self.input.delimited_span(
            position,
            open,
            close,
            self.parser.limits.foreign_nesting,
        ) {
            Ok(Some(span)) => span,
            Ok(None) => return Ok(()),
            Err(DelimitedSpanError::NestingLimit) => {
                return Err(RuntimeError::ForeignNestingLimit { byte: position });
            },
            Err(DelimitedSpanError::Unterminated) => {
                return Err(RuntimeError::ForeignLanguage {
                    byte: position,
                    message: format!("unterminated foreign-language region `{open}` ... `{close}`"),
                });
            },
        };
        let key = (open.to_string(), close.to_string(), position, end);
        let node = if let Some(node) = self.foreign.get(&key) {
            *node
        } else {
            let node = self.push_node(ForestNode::Foreign {
                open: open.into(),
                close: close.into(),
                start: position,
                content_start,
                content_end,
                end,
            })?;
            self.foreign.insert(key, node);
            node
        };
        self.advance(item, node, self.canonical_position(end))
    }

    fn advance(&mut self, item: ItemKey, child: NodeId, end: usize) -> Result<(), RuntimeError> {
        let next = ItemKey {
            rule: item.rule,
            dot: item.dot + 1,
            origin: item.origin,
            end,
        };
        let previous = (item.dot > 0)
            .then(|| self.intermediate.get(&item).copied())
            .flatten();
        self.add_item(next, Some(PackedPair { previous, child }))
    }

    fn add_item(&mut self, item: ItemKey, packing: Option<PackedPair>) -> Result<(), RuntimeError> {
        if let Some(packing) = packing {
            let node = if let Some(node) = self.intermediate.get(&item) {
                *node
            } else {
                let node =
                    self.push_node(ForestNode::Intermediate { item, alternatives: Vec::new() })?;
                self.intermediate.insert(item, node);
                node
            };
            if let ForestNode::Intermediate { alternatives, .. } = &mut self.nodes[node as usize] {
                if !alternatives.contains(&packing) {
                    alternatives.push(packing);
                }
            }
        }
        if self.items.insert(item) {
            if self.items.len() > self.parser.limits.parse_items {
                return Err(RuntimeError::ParseItemLimit);
            }
            self.queue.push_back(item);
        }
        Ok(())
    }

    fn complete(
        &mut self,
        nonterminal: u32,
        start: usize,
        end: usize,
        rule: u32,
        prefix: Option<NodeId>,
    ) -> Result<(), RuntimeError> {
        let key = (nonterminal, start, end);
        let mut new_node = false;
        let node = if let Some(node) = self.nonterminals.get(&key) {
            *node
        } else {
            new_node = true;
            let node = self.push_node(ForestNode::Nonterminal {
                start,
                end,
                alternatives: Vec::new(),
                template_hole: None,
            })?;
            self.nonterminals.insert(key, node);
            self.completed
                .entry((nonterminal, start))
                .or_default()
                .push(node);
            node
        };
        let alternative = CompletedRule { rule, prefix };
        if let ForestNode::Nonterminal { alternatives, .. } = &mut self.nodes[node as usize] {
            if !alternatives.contains(&alternative) {
                alternatives.push(alternative);
            }
        }
        if new_node {
            for waiting in self
                .waiting
                .get(&(start, nonterminal))
                .cloned()
                .unwrap_or_default()
            {
                self.advance(waiting, node, end)?;
            }
        }
        Ok(())
    }

    fn complete_template_hole(
        &mut self,
        nonterminal: u32,
        position: usize,
    ) -> Result<(), RuntimeError> {
        let position = self.canonical_position(position);
        let Some(hole) = self.holes.get(&position).copied() else {
            return Ok(());
        };
        let Some(category) = self.parser.grammar.categories.get(nonterminal as usize) else {
            return Ok(());
        };
        if !category.admits_variables
            || hole
                .category
                .is_some_and(|expected| expected.0 != nonterminal)
        {
            return Ok(());
        }
        let key = (nonterminal, position, hole.end);
        if !self.hole_nonterminals.insert(key) {
            return Ok(());
        }

        let mut new_node = false;
        let node = if let Some(node) = self.nonterminals.get(&key) {
            *node
        } else {
            new_node = true;
            let node = self.push_node(ForestNode::Nonterminal {
                start: position,
                end: hole.end,
                alternatives: Vec::new(),
                template_hole: Some((hole.id, CategoryId(nonterminal))),
            })?;
            self.nonterminals.insert(key, node);
            self.completed
                .entry((nonterminal, position))
                .or_default()
                .push(node);
            node
        };
        if let ForestNode::Nonterminal { template_hole, .. } = &mut self.nodes[node as usize] {
            *template_hole = Some((hole.id, CategoryId(nonterminal)));
        }
        if new_node {
            for waiting in self
                .waiting
                .get(&(position, nonterminal))
                .cloned()
                .unwrap_or_default()
            {
                self.advance(waiting, node, hole.end)?;
            }
        }
        Ok(())
    }

    fn canonical_position(&self, mut position: usize) -> usize {
        while let Some(lexeme) = self.lexemes.get(&position) {
            if !lexeme.hidden {
                break;
            }
            position = lexeme.end;
        }
        position
    }

    fn push_node(&mut self, node: ForestNode) -> Result<NodeId, RuntimeError> {
        if self.nodes.len() >= self.parser.limits.forest_nodes {
            return Err(RuntimeError::ForestNodeLimit);
        }
        let id = self.nodes.len() as NodeId;
        self.nodes.push(node);
        Ok(id)
    }

    fn realize(
        &self,
        root: NodeId,
        context: &mut RealizationContext,
    ) -> Result<Vec<SemanticPath>, RuntimeError> {
        self.realize_node(root, context)
    }

    fn realize_weighted(&self, roots: Vec<NodeId>) -> Result<Vec<WeightedParse>, RuntimeError> {
        let mut output = Vec::new();
        let mut realization = RealizationContext::new(self.parser.limits.semantic_results);
        for root in roots {
            for path in self.realize(root, &mut realization)? {
                if path.values.len() == 1 {
                    output.push(WeightedParse {
                        syntax: path.values[0].syntax.clone(),
                        value: path.values[0].value.clone(),
                        cost: path.cost,
                        rank: path.rank,
                        production: path.top_production,
                    });
                }
            }
        }
        Ok(output)
    }

    fn realize_node(
        &self,
        node: NodeId,
        context: &mut RealizationContext,
    ) -> Result<Vec<SemanticPath>, RuntimeError> {
        enum RealizeTask {
            Enter(NodeId),
            Exit(NodeId),
        }

        let mut tasks = vec![RealizeTask::Enter(node)];
        while let Some(task) = tasks.pop() {
            match task {
                RealizeTask::Enter(node) => {
                    if context.memo.contains_key(&node) {
                        continue;
                    }
                    if !context.active.insert(node) {
                        return Err(RuntimeError::ForestCycle);
                    }
                    tasks.push(RealizeTask::Exit(node));
                    match &self.nodes[node as usize] {
                        ForestNode::Intermediate { alternatives, .. } => {
                            for pair in alternatives.iter().rev() {
                                tasks.push(RealizeTask::Enter(pair.child));
                                if let Some(previous) = pair.previous {
                                    tasks.push(RealizeTask::Enter(previous));
                                }
                            }
                        },
                        ForestNode::Nonterminal { alternatives, .. } => {
                            for prefix in alternatives
                                .iter()
                                .rev()
                                .filter_map(|alternative| alternative.prefix)
                            {
                                tasks.push(RealizeTask::Enter(prefix));
                            }
                        },
                        ForestNode::Terminal { .. } | ForestNode::Foreign { .. } => {},
                    }
                },
                RealizeTask::Exit(node) => {
                    let result = match self.nodes[node as usize].clone() {
                        ForestNode::Terminal { token, start, end, alternative } => {
                            let text = self.input.slice(start, end).ok_or_else(|| {
                                RuntimeError::Reduction(
                                    "terminal crosses an FLT hole boundary".into(),
                                )
                            })?;
                            consume_semantic_result(&mut context.remaining_results)?;
                            vec![SemanticPath::value_with_rank(
                                self.parser.decode_token(token, text)?,
                                DerivationRank::lexical(
                                    start as u32,
                                    text.len() as u32,
                                    alternative,
                                ),
                            )]
                        },
                        ForestNode::Foreign {
                            open,
                            close,
                            start,
                            content_start,
                            content_end,
                            end,
                        } => {
                            let value = self
                                .parser
                                .parse_foreign_committed(
                                    &open,
                                    &close,
                                    self.input.slice(content_start, content_end).ok_or_else(
                                        || RuntimeError::ForeignLanguage {
                                            byte: start,
                                            message: "foreign-language region crosses an FLT hole boundary"
                                                .into(),
                                        },
                                    )?,
                                    SourceSpan { start: start as u32, end: end as u32 },
                                )
                                .map_err(|message| RuntimeError::ForeignLanguage {
                                    byte: start,
                                    message,
                                })?;
                            consume_semantic_result(&mut context.remaining_results)?;
                            vec![SemanticPath::value_with_rank(
                                value,
                                DerivationRank::lexical(start as u32, open.len() as u32, 0),
                            )]
                        },
                        ForestNode::Intermediate { item, alternatives } => {
                            let rule = &self.parser.image.engine.runtime_rules[item.rule as usize];
                            let symbol = &self.parser.image.engine.runtime_symbols
                                [(rule.symbol_start + u32::from(item.dot - 1)) as usize];
                            let capture = match symbol {
                                RuntimeSymbol::Token { capture, .. }
                                | RuntimeSymbol::Nonterminal { capture, .. }
                                | RuntimeSymbol::Foreign { capture, .. } => *capture,
                            };
                            let mut paths = Vec::new();
                            let mut unique = HashSet::new();
                            for pair in alternatives {
                                let empty = [SemanticPath::empty()];
                                let previous = pair.previous.map_or(empty.as_slice(), |previous| {
                                    context
                                        .memo
                                        .get(&previous)
                                        .expect("realization PDA completed predecessor")
                                });
                                let children = context
                                    .memo
                                    .get(&pair.child)
                                    .expect("realization PDA completed child");
                                for left in previous {
                                    for right in children {
                                        let mut joined = left.join(right)?;
                                        if !capture {
                                            joined.values.truncate(left.values.len());
                                        }
                                        joined.child_tops.truncate(left.child_tops.len());
                                        joined.child_tops.push(right.top_production);
                                        push_semantic(
                                            &mut paths,
                                            &mut unique,
                                            joined,
                                            &mut context.remaining_results,
                                        )?;
                                    }
                                }
                            }
                            paths
                        },
                        ForestNode::Nonterminal { start, end, alternatives, template_hole } => {
                            let mut paths = Vec::new();
                            let mut unique = HashSet::new();
                            if let Some((id, category)) = template_hole {
                                push_semantic(
                                    &mut paths,
                                    &mut unique,
                                    SemanticPath::value(DynamicValue::TemplateHole {
                                        id,
                                        category,
                                    }),
                                    &mut context.remaining_results,
                                )?;
                            }
                            for alternative in alternatives {
                                let rule = &self.parser.image.engine.runtime_rules
                                    [alternative.rule as usize];
                                let empty = [SemanticPath::empty()];
                                let prefixes =
                                    alternative.prefix.map_or(empty.as_slice(), |prefix| {
                                        context
                                            .memo
                                            .get(&prefix)
                                            .expect("realization PDA completed prefix")
                                    });
                                for prefix in prefixes {
                                    if !self.precedence_valid(rule, &prefix.child_tops) {
                                        continue;
                                    }
                                    let values =
                                        self.apply_rule(rule, &prefix.values, start, end)?;
                                    let cost = prefix.cost.times(&rule.cost);
                                    let rank = match rule.production {
                                        Some(production) => {
                                            let definition = &self.parser.grammar.productions
                                                [production.0 as usize];
                                            prefix.rank.clone().complete_production(
                                                start as u32,
                                                SourceRuleRank {
                                                    source_category: definition.result.0,
                                                    declaration: production.0,
                                                },
                                            )
                                        },
                                        None => prefix.rank.clone(),
                                    };
                                    push_semantic(
                                        &mut paths,
                                        &mut unique,
                                        SemanticPath {
                                            values,
                                            cost,
                                            rank,
                                            top_production: rule.production,
                                            child_tops: Vec::new(),
                                        },
                                        &mut context.remaining_results,
                                    )?;
                                }
                            }
                            paths
                        },
                    };
                    context.active.remove(&node);
                    context.memo.insert(node, result);
                },
            }
        }
        Ok(context
            .memo
            .get(&node)
            .expect("realization PDA completes its root")
            .clone())
    }

    fn apply_rule(
        &self,
        rule: &RuntimeRule,
        values: &[SemanticValue],
        start: usize,
        end: usize,
    ) -> Result<Vec<SemanticValue>, RuntimeError> {
        let span = SourceSpan {
            start: start as u32,
            end: end.min(self.input.end) as u32,
        };
        Ok(match rule.semantic {
            RuntimeRuleSemantic::Reduce => {
                let production = rule
                    .production
                    .ok_or(RuntimeError::BadReduction(rule.lhs))?;
                let definition = &self.parser.grammar.productions[production.0 as usize];
                let reduction = self
                    .parser
                    .grammar
                    .reductions
                    .get(definition.reduction as usize)
                    .ok_or(RuntimeError::BadReduction(definition.reduction))?;
                let semantic_inputs = values
                    .iter()
                    .map(|value| value.value.clone())
                    .collect::<Vec<_>>();
                let syntax_inputs = values
                    .iter()
                    .map(|value| value.syntax.clone())
                    .collect::<Vec<_>>();
                let semantic_term = reduction
                    .apply(&semantic_inputs, &[], span)
                    .map_err(|error| RuntimeError::Reduction(format!("{error:?}")))?;
                let syntax_term = reduction
                    .apply(&syntax_inputs, &[], span)
                    .map_err(|error| RuntimeError::Reduction(format!("{error:?}")))?;
                let value = if let Some(evaluation) = &reduction.evaluation {
                    self.parser
                        .evaluate_native(evaluation, &semantic_inputs, span)?
                } else {
                    DynamicValue::Term(Box::new(semantic_term))
                };
                vec![SemanticValue {
                    syntax: DynamicValue::Term(Box::new(syntax_term)),
                    value,
                }]
            },
            RuntimeRuleSemantic::EmptyOptional { slots } => (0..slots)
                .map(|_| SemanticValue::same(DynamicValue::Sequence(Vec::new())))
                .collect(),
            RuntimeRuleSemantic::EmptyCollection { layout } => (0..layout.slots())
                .map(|index| {
                    let value = DynamicValue::collection(
                        layout
                            .kind(index as usize)
                            .expect("verified collection layout"),
                        Vec::new(),
                    )
                    .map_err(|error| RuntimeError::Reduction(format!("{error:?}")))?;
                    Ok(SemanticValue::same(value))
                })
                .collect::<Result<Vec<_>, _>>()?,
            RuntimeRuleSemantic::PresentOptional { slots } => {
                if values.len() != slots as usize {
                    return Err(RuntimeError::Reduction(format!(
                        "auxiliary semantic arity {} != {}",
                        values.len(),
                        slots
                    )));
                }
                values
                    .iter()
                    .cloned()
                    .map(|value| SemanticValue {
                        syntax: DynamicValue::Sequence(vec![value.syntax]),
                        value: DynamicValue::Sequence(vec![value.value]),
                    })
                    .collect()
            },
            RuntimeRuleSemantic::SingletonCollection { layout } => {
                let slots = layout.slots();
                if values.len() != slots as usize {
                    return Err(RuntimeError::Reduction(format!(
                        "collection singleton arity {} != {}",
                        values.len(),
                        slots
                    )));
                }
                values
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(index, value)| {
                        let kind = layout.kind(index).expect("verified collection layout");
                        SemanticValue {
                            syntax: DynamicValue::Collection { kind, entries: vec![value.syntax] },
                            value: DynamicValue::Collection { kind, entries: vec![value.value] },
                        }
                    })
                    .collect()
            },
            RuntimeRuleSemantic::AppendCollection { layout } => {
                let slots = layout.slots();
                if values.len() != slots as usize * 2 {
                    return Err(RuntimeError::Reduction(format!(
                        "collection append arity {} != {}",
                        values.len(),
                        slots as usize * 2
                    )));
                }
                let mut output = Vec::with_capacity(slots as usize);
                for index in 0..slots as usize {
                    let kind = layout.kind(index).expect("verified collection layout");
                    let prefix = &values[index];
                    let last = &values[index + slots as usize];
                    output.push(SemanticValue {
                        syntax: DynamicValue::append_collection(
                            kind,
                            prefix.syntax.clone(),
                            last.syntax.clone(),
                        )
                        .map_err(|error| RuntimeError::Reduction(format!("{error:?}")))?,
                        value: DynamicValue::append_collection(
                            kind,
                            prefix.value.clone(),
                            last.value.clone(),
                        )
                        .map_err(|error| RuntimeError::Reduction(format!("{error:?}")))?,
                    });
                }
                output
            },
            RuntimeRuleSemantic::FinalizeCollection { layout } => {
                let slots = layout.slots();
                if values.len() != slots as usize {
                    return Err(RuntimeError::Reduction(format!(
                        "collection finalize arity {} != {}",
                        values.len(),
                        slots
                    )));
                }
                values
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(index, value)| {
                        let expected = layout.kind(index).expect("verified collection layout");
                        let finalize = |value: DynamicValue| {
                            let (kind, entries) = value.into_collection_parts().map_err(|_| {
                                RuntimeError::Reduction(
                                    "collection finalizer received a non-collection".into(),
                                )
                            })?;
                            if kind != expected {
                                return Err(RuntimeError::Reduction(
                                    "collection finalizer received the wrong collection kind"
                                        .into(),
                                ));
                            }
                            DynamicValue::collection(kind, entries)
                                .map_err(|error| RuntimeError::Reduction(format!("{error:?}")))
                        };
                        Ok(SemanticValue {
                            syntax: finalize(value.syntax)?,
                            value: finalize(value.value)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?
            },
            RuntimeRuleSemantic::Tuple { slots } => {
                if values.len() != slots as usize {
                    return Err(RuntimeError::Reduction(format!(
                        "tuple arity {} != {}",
                        values.len(),
                        slots
                    )));
                }
                vec![SemanticValue {
                    syntax: DynamicValue::Sequence(
                        values.iter().map(|value| value.syntax.clone()).collect(),
                    ),
                    value: DynamicValue::Sequence(
                        values.iter().map(|value| value.value.clone()).collect(),
                    ),
                }]
            },
            RuntimeRuleSemantic::Unit { slots } => (0..slots)
                .map(|_| SemanticValue::same(DynamicValue::Unit))
                .collect(),
        })
    }

    fn precedence_valid(&self, rule: &RuntimeRule, child_tops: &[Option<ProductionId>]) -> bool {
        let Some(parent_id) = rule.production else {
            return true;
        };
        let parent = &self.parser.grammar.productions[parent_id.0 as usize];
        let Some(parent_bp) = parent.precedence.binding_power else {
            return true;
        };
        let start = rule.symbol_start as usize;
        let end = start + rule.symbol_len as usize;
        let category_children = self.parser.image.engine.runtime_symbols[start..end]
            .iter()
            .enumerate()
            .filter_map(|(index, symbol)| match symbol {
                RuntimeSymbol::Nonterminal { nonterminal, .. }
                    if *nonterminal == parent.result.0 =>
                {
                    Some(index)
                },
                _ => None,
            })
            .collect::<Vec<_>>();
        let tighter = |child: Option<ProductionId>, allow_equal: bool| {
            child
                .and_then(|id| self.parser.grammar.productions.get(id.0 as usize))
                .and_then(|production| production.precedence.binding_power)
                .is_none_or(|binding_power| {
                    binding_power > parent_bp || (allow_equal && binding_power == parent_bp)
                })
        };
        if parent.classification.infix && category_children.len() >= 2 {
            let left = child_tops.get(category_children[0]).copied().flatten();
            let right = child_tops
                .get(*category_children.last().expect("two children"))
                .copied()
                .flatten();
            match parent.precedence.associativity {
                Associativity::Left => tighter(left, true) && tighter(right, false),
                Associativity::Right => tighter(left, false) && tighter(right, true),
                Associativity::NonAssociative => tighter(left, false) && tighter(right, false),
            }
        } else if parent.classification.prefix {
            category_children
                .last()
                .is_none_or(|index| tighter(child_tops.get(*index).copied().flatten(), true))
        } else if parent.classification.postfix {
            category_children
                .first()
                .is_none_or(|index| tighter(child_tops.get(*index).copied().flatten(), true))
        } else {
            true
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SemanticValue {
    syntax: DynamicValue,
    value: DynamicValue,
}

impl SemanticValue {
    fn same(value: DynamicValue) -> Self {
        Self { syntax: value.clone(), value }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SemanticPath {
    values: Vec<SemanticValue>,
    cost: ExactParseCost,
    rank: DerivationRank,
    top_production: Option<ProductionId>,
    child_tops: Vec<Option<ProductionId>>,
}

impl SemanticPath {
    fn empty() -> Self {
        Self {
            values: Vec::new(),
            cost: ExactParseCost::default(),
            rank: DerivationRank::default(),
            top_production: None,
            child_tops: Vec::new(),
        }
    }

    fn value(value: DynamicValue) -> Self {
        Self {
            values: vec![SemanticValue::same(value)],
            ..Self::empty()
        }
    }

    fn value_with_rank(value: DynamicValue, rank: DerivationRank) -> Self {
        Self {
            values: vec![SemanticValue::same(value)],
            rank,
            ..Self::empty()
        }
    }

    fn join(&self, rhs: &Self) -> Result<Self, RuntimeError> {
        let mut values = self.values.clone();
        values.extend(rhs.values.iter().cloned());
        let mut child_tops = self.child_tops.clone();
        child_tops.extend(rhs.child_tops.iter().copied());
        Ok(Self {
            values,
            cost: self.cost.times(&rhs.cost),
            rank: self.rank.combine(&rhs.rank),
            top_production: rhs.top_production,
            child_tops,
        })
    }
}

fn push_semantic(
    output: &mut Vec<SemanticPath>,
    unique: &mut HashSet<SemanticPath>,
    value: SemanticPath,
    budget: &mut usize,
) -> Result<(), RuntimeError> {
    if !unique.insert(value.clone()) {
        return Ok(());
    }
    consume_semantic_result(budget)?;
    output.push(value);
    Ok(())
}

fn consume_semantic_result(budget: &mut usize) -> Result<(), RuntimeError> {
    if *budget == 0 {
        return Err(RuntimeError::SemanticResultLimit);
    }
    *budget -= 1;
    Ok(())
}

enum DelimitedSpanError {
    Unterminated,
    NestingLimit,
}

fn delimited_span(
    source: &str,
    position: usize,
    open: &str,
    close: &str,
    max_nesting: u32,
) -> Result<Option<(usize, usize, usize)>, DelimitedSpanError> {
    if position > source.len() || open.is_empty() || close.is_empty() || open == close {
        return Ok(None);
    }
    if !source[position..].starts_with(open) {
        return Ok(None);
    }
    let content_start = position + open.len();
    let mut cursor = content_start;
    let mut depth = 1u32;
    while cursor <= source.len() {
        if source[cursor..].starts_with(open) {
            depth = depth
                .checked_add(1)
                .ok_or(DelimitedSpanError::NestingLimit)?;
            if depth > max_nesting {
                return Err(DelimitedSpanError::NestingLimit);
            }
            cursor += open.len();
        } else if source[cursor..].starts_with(close) {
            depth -= 1;
            if depth == 0 {
                return Ok(Some((content_start, cursor, cursor + close.len())));
            }
            cursor += close.len();
        } else {
            let Some(character) = source[cursor..].chars().next() else {
                break;
            };
            cursor += character.len_utf8();
        }
    }
    Err(DelimitedSpanError::Unterminated)
}

fn decode_integer(text: &str, radix: u8) -> Option<i128> {
    let radix = u32::from(radix);
    let (negative, digits) = text
        .strip_prefix('-')
        .map_or((false, text), |value| (true, value));
    let digits = digits.strip_prefix('+').unwrap_or(digits);
    let value = i128::from_str_radix(digits, radix).ok()?;
    Some(if negative { -value } else { value })
}

fn decode_hex(text: &str) -> Option<Vec<u8>> {
    let text = text.strip_prefix("0x").unwrap_or(text);
    if !text.len().is_multiple_of(2) {
        return None;
    }
    (0..text.len())
        .step_by(2)
        .map(|index| u8::from_str_radix(&text[index..index + 2], 16).ok())
        .collect()
}

fn default_evaluate(
    evaluation: &NativeEvaluation,
    inputs: &[DynamicValue],
) -> Result<DynamicValue, String> {
    match evaluation {
        NativeEvaluation::Operator(operator) => evaluate_operator(operator, inputs),
        NativeEvaluation::Carrier { kind, .. } => evaluate_carrier(kind, inputs),
        NativeEvaluation::Handler(capability) => {
            Err(format!("unavailable native evaluator capability `{capability}`"))
        },
        NativeEvaluation::Source { .. } => Err("runtime source evaluation is forbidden".into()),
    }
}

fn evaluate_carrier(kind: &str, inputs: &[DynamicValue]) -> Result<DynamicValue, String> {
    let [value] = inputs else {
        return Err(format!("carrier `{kind}` expects one input"));
    };
    match (kind, value) {
        ("int", DynamicValue::Integer(value)) => Ok(DynamicValue::Integer(*value)),
        ("int", DynamicValue::Text(value)) => value
            .parse::<i128>()
            .map(DynamicValue::Integer)
            .map_err(|_| "invalid integer carrier value".into()),
        ("bool", DynamicValue::Boolean(value)) => Ok(DynamicValue::Boolean(*value)),
        ("bool", DynamicValue::Text(value)) if value == "true" => Ok(DynamicValue::Boolean(true)),
        ("bool", DynamicValue::Text(value)) if value == "false" => Ok(DynamicValue::Boolean(false)),
        ("str", DynamicValue::Text(value)) => Ok(DynamicValue::Text(value.clone())),
        ("rat" | "fixed" | "float", DynamicValue::Text(value)) => {
            Ok(DynamicValue::Text(value.clone()))
        },
        _ => Err(format!("value is incompatible with carrier `{kind}`")),
    }
}

fn evaluate_operator(operator: &str, inputs: &[DynamicValue]) -> Result<DynamicValue, String> {
    let integers = || match inputs {
        [DynamicValue::Integer(left), DynamicValue::Integer(right)] => Some((*left, *right)),
        _ => None,
    };
    let booleans = || match inputs {
        [DynamicValue::Boolean(left), DynamicValue::Boolean(right)] => Some((*left, *right)),
        _ => None,
    };
    match operator {
        "add" => integers()
            .and_then(|(a, b)| a.checked_add(b))
            .map(DynamicValue::Integer),
        "sub" => integers()
            .and_then(|(a, b)| a.checked_sub(b))
            .map(DynamicValue::Integer),
        "mul" => integers()
            .and_then(|(a, b)| a.checked_mul(b))
            .map(DynamicValue::Integer),
        "div" => integers()
            .and_then(|(a, b)| a.checked_div(b))
            .map(DynamicValue::Integer),
        "mod" => integers()
            .and_then(|(a, b)| a.checked_rem(b))
            .map(DynamicValue::Integer),
        "neg" => match inputs {
            [DynamicValue::Integer(value)] => value.checked_neg().map(DynamicValue::Integer),
            _ => None,
        },
        "eq" => match inputs {
            [left, right] => Some(DynamicValue::Boolean(left == right)),
            _ => None,
        },
        "ne" => match inputs {
            [left, right] => Some(DynamicValue::Boolean(left != right)),
            _ => None,
        },
        "lt" => integers().map(|(a, b)| DynamicValue::Boolean(a < b)),
        "gt" => integers().map(|(a, b)| DynamicValue::Boolean(a > b)),
        "le" => integers().map(|(a, b)| DynamicValue::Boolean(a <= b)),
        "ge" => integers().map(|(a, b)| DynamicValue::Boolean(a >= b)),
        "and" => booleans().map(|(a, b)| DynamicValue::Boolean(a && b)),
        "or" => booleans().map(|(a, b)| DynamicValue::Boolean(a || b)),
        "xor" => booleans().map(|(a, b)| DynamicValue::Boolean(a ^ b)),
        "not" => match inputs {
            [DynamicValue::Boolean(value)] => Some(DynamicValue::Boolean(!value)),
            _ => None,
        },
        "concat" => match inputs {
            [DynamicValue::Text(left), DynamicValue::Text(right)] => {
                Some(DynamicValue::Text(format!("{left}{right}")))
            },
            [DynamicValue::Sequence(left), DynamicValue::Sequence(right)] => {
                let mut output = left.clone();
                output.extend(right.iter().cloned());
                Some(DynamicValue::Sequence(output))
            },
            [
                DynamicValue::Collection { kind: left_kind, entries: left },
                DynamicValue::Collection { kind: right_kind, entries: right },
            ] if left_kind == right_kind => {
                let mut entries = left.clone();
                entries.extend(right.iter().cloned());
                DynamicValue::collection(*left_kind, entries).ok()
            },
            _ => None,
        },
        "len" => match inputs {
            [DynamicValue::Text(value)] => {
                Some(DynamicValue::Integer(value.chars().count() as i128))
            },
            [DynamicValue::Bytes(value)] => Some(DynamicValue::Integer(value.len() as i128)),
            [DynamicValue::Sequence(value)] => Some(DynamicValue::Integer(value.len() as i128)),
            [DynamicValue::Collection { entries, .. }] => {
                Some(DynamicValue::Integer(entries.len() as i128))
            },
            _ => None,
        },
        _ => None,
    }
    .ok_or_else(|| format!("operator `{operator}` received invalid inputs or overflowed"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        BuiltinToken, Carrier, Category, ConstructorId, EngineTables, FieldSource, IndexWidth,
        LexerImage, LexerMode, LexerState, LexerTransition, ModeTransition, ParserImageKind,
        Precedence, Production, ProductionClass, ReductionPlan, Reservation, RuntimeRule,
        RuntimeRuleSemantic, RuntimeSymbol, TokenDefinition,
    };

    fn integer_grammar() -> (GrammarCoreV1, ParserImageV1) {
        let mut grammar = GrammarCoreV1::new("Integer");
        grammar.categories.push(Category {
            id: CategoryId(0),
            name: "Expr".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        grammar.tokens.push(TokenDefinition {
            id: TokenId(0),
            name: "integer".into(),
            pattern: TokenPattern::Builtin(BuiltinToken::Integer),
            category: Some(CategoryId(0)),
            evaluation: None,
            priority: 1,
            mode: ModeId(0),
            channel: "main".into(),
            transition: ModeTransition::default(),
            decoder: TokenDecoder::Integer { radix: None },
            reservation: Reservation::None,
        });
        grammar.modes = vec![LexerMode {
            id: ModeId(0),
            name: "default".into(),
            token_ids: vec![TokenId(0)],
            raw: false,
        }];
        grammar.reductions.push(ReductionPlan {
            output_category: CategoryId(0),
            constructor: ConstructorId(0),
            input_arity: 1,
            fields: vec![FieldSource::Input(0)],
            evaluation: None,
            evaluation_mode: None,
            tier: None,
        });
        grammar.productions.push(Production {
            id: ProductionId(0),
            constructor: ConstructorId(0),
            label: "Int".into(),
            result: CategoryId(0),
            syntax: vec![crate::SyntaxItem::CaptureToken {
                token: TokenId(0),
                slot: "value".into(),
            }],
            precedence: Precedence::default(),
            classification: ProductionClass::default(),
            reduction: 0,
            provenance: None,
        });
        let image = ParserImageV1 {
            magic: crate::PARSER_IMAGE_MAGIC,
            abi: crate::PARSER_IMAGE_ABI_V1,
            compiler_abi: "test".into(),
            unicode_version: "test".into(),
            core_fingerprint: grammar.fingerprint().expect("fingerprint"),
            kind: ParserImageKind::Executable,
            index_width: IndexWidth::U8,
            exact: true,
            lexer: LexerImage {
                mode_starts: vec![0],
                states: vec![
                    LexerState {
                        transition_start: 0,
                        transition_len: 1,
                        accept: Vec::new(),
                    },
                    LexerState {
                        transition_start: 1,
                        transition_len: 1,
                        accept: vec![TokenId(0)],
                    },
                ],
                transitions: vec![
                    LexerTransition { start: b'0', end: b'9', target: 1 },
                    LexerTransition { start: b'0', end: b'9', target: 1 },
                ],
            },
            reductions: grammar.reductions.clone(),
            engine: EngineTables {
                nonterminal_count: 1,
                start_nonterminals: vec![0],
                nonterminal_rule_starts: vec![0, 1],
                runtime_rules: vec![RuntimeRule {
                    lhs: 0,
                    symbol_start: 0,
                    symbol_len: 1,
                    production: Some(ProductionId(0)),
                    semantic: RuntimeRuleSemantic::Reduce,
                    cost: ExactParseCost::default(),
                }],
                runtime_symbols: vec![RuntimeSymbol::Token { token: TokenId(0), capture: true }],
                same_span_ranks: vec![0],
                category_min_spans: vec![1],
                ..EngineTables::default()
            },
            limits: grammar.limits,
        };
        (grammar, image)
    }

    #[test]
    fn table_driven_parser_builds_dynamic_terms() {
        let (grammar, image) = integer_grammar();
        let host = DefaultRuntimeHost;
        let parser = RuntimeParser::new(&grammar, &image, "test", "test", &host).expect("parser");
        let parsed = parser.parse("123").expect("parse");
        let DynamicValue::Term(term) = &parsed[0].value else {
            panic!("term")
        };
        assert_eq!(term.fields, vec![DynamicValue::Integer(123)]);
        assert_eq!(parsed[0].syntax, parsed[0].value);
    }

    #[test]
    fn equal_cost_ambiguity_retains_both_derivations_and_elects_by_rank() {
        let (mut grammar, mut image) = integer_grammar();
        grammar.weight_profile = crate::WeightProfile::Exact {
            default: ExactParseCost::from_ticks(7).expect("finite exact cost"),
            retain_all_alternatives: true,
        };

        let mut reduction = grammar.reductions[0].clone();
        reduction.constructor = ConstructorId(1);
        grammar.reductions.push(reduction);
        let mut production = grammar.productions[0].clone();
        production.id = ProductionId(1);
        production.constructor = ConstructorId(1);
        production.label = "AlternativeInt".into();
        production.reduction = 1;
        grammar.productions.push(production);

        image.core_fingerprint = grammar.fingerprint().expect("fingerprint");
        image.reductions = grammar.reductions.clone();
        image.engine = crate::normalize_runtime_engine(&grammar).expect("normalize");

        let parser = RuntimeParser::new(&grammar, &image, "test", "test", &DefaultRuntimeHost)
            .expect("parser");
        let parsed = parser.parse("123").expect("ambiguous parse");

        assert_eq!(parsed.len(), 2);
        assert_eq!(
            parsed.iter().map(|result| result.cost).collect::<Vec<_>>(),
            vec![
                ExactParseCost::from_ticks(7).expect("finite"),
                ExactParseCost::from_ticks(7).expect("finite"),
            ]
        );
        assert_ne!(parsed[0].rank, parsed[1].rank);
        assert_eq!(
            parsed
                .iter()
                .map(|result| result.rank.positions()[0].productions[0].declaration)
                .collect::<Vec<_>>(),
            vec![0, 1]
        );
    }

    struct BuiltinOverrideHost;

    impl RuntimeHost for BuiltinOverrideHost {
        fn evaluate(
            &self,
            _evaluation: &NativeEvaluation,
            _inputs: &[DynamicValue],
            _span: SourceSpan,
        ) -> Result<DynamicValue, String> {
            Ok(DynamicValue::Unit)
        }
    }

    #[test]
    fn native_evaluation_retains_the_constructor_recognition_witness() {
        let (mut grammar, mut image) = integer_grammar();
        grammar.reductions[0].evaluation = Some(NativeEvaluation::Carrier {
            kind: "int".into(),
            parameters: BTreeMap::new(),
        });
        image.reductions = grammar.reductions.clone();
        image.core_fingerprint = grammar.fingerprint().expect("fingerprint");

        let parser = RuntimeParser::new(&grammar, &image, "test", "test", &BuiltinOverrideHost)
            .expect("parser");
        let parsed = parser.parse("123").expect("parse");

        assert_eq!(parsed[0].value, DynamicValue::Integer(123));
        let DynamicValue::Term(term) = &parsed[0].syntax else {
            panic!("native evaluation must not erase the recognized constructor")
        };
        assert_eq!(term.category, CategoryId(0));
        assert_eq!(term.constructor, ConstructorId(0));
        assert_eq!(term.fields, vec![DynamicValue::Integer(123)]);
    }

    #[test]
    fn runtime_source_cannot_route_through_a_host_override() {
        let (mut grammar, mut image) = integer_grammar();
        grammar.reductions[0].evaluation = Some(NativeEvaluation::Source {
            semantics: vec!["Rust".into()],
            text: "attacker_selected()".into(),
        });
        image.reductions = grammar.reductions.clone();
        image.core_fingerprint = grammar.fingerprint().expect("fingerprint");
        let parser = RuntimeParser::new(&grammar, &image, "test", "test", &BuiltinOverrideHost)
            .expect("parser image remains structurally valid");
        assert!(matches!(parser.parse("123"), Err(RuntimeError::NativeSourceForbidden)));
    }

    struct RevokingDecoderHost {
        changed: std::sync::atomic::AtomicBool,
    }

    impl RuntimeHost for RevokingDecoderHost {
        fn capability_manifest(
            &self,
            key: &RuntimeCapabilityKey,
        ) -> Option<RuntimeCapabilityManifest> {
            Some(RuntimeCapabilityManifest {
                key: key.clone(),
                code_commitment: if self.changed.load(std::sync::atomic::Ordering::SeqCst) {
                    [2; 32]
                } else {
                    [1; 32]
                },
                abi: "revoking-decoder/1".into(),
                effects: [crate::RuntimeEffect::Reduce].into_iter().collect(),
                cost: crate::RuntimeLogicalCost {
                    base: 1,
                    per_input_byte: 1,
                    per_value: 0,
                    maximum: 1_024,
                },
            })
        }

        fn decode_token(&self, _capability: &str, text: &str) -> Result<DynamicValue, String> {
            self.changed
                .store(true, std::sync::atomic::Ordering::SeqCst);
            Ok(DynamicValue::Text(text.into()))
        }
    }

    #[test]
    fn changed_manifest_during_callback_discards_the_result() {
        let (mut grammar, mut image) = integer_grammar();
        grammar.tokens[0].decoder = TokenDecoder::Capability("test/decoder".into());
        grammar
            .capabilities
            .insert(crate::Capability::TokenDecoder("test/decoder".into()));
        image.core_fingerprint = grammar.fingerprint().expect("fingerprint");
        let host = RevokingDecoderHost {
            changed: std::sync::atomic::AtomicBool::new(false),
        };
        let parser = RuntimeParser::new(&grammar, &image, "test", "test", &host).expect("bind");
        assert!(matches!(
            parser.parse("123"),
            Err(RuntimeError::Capability(RuntimeCapabilityError::Changed(_)))
        ));
    }

    #[test]
    fn structural_template_hole_is_a_category_edge_not_source_text() {
        let (mut grammar, mut image) = integer_grammar();
        grammar.categories[0].admits_variables = true;
        image.core_fingerprint = grammar.fingerprint().expect("fingerprint");
        let host = DefaultRuntimeHost;
        let parser = RuntimeParser::new(&grammar, &image, "test", "test", &host).expect("parser");
        let parsed = parser
            .parse_template(
                &[RuntimeTemplatePiece::Hole(0)],
                &[RuntimeTemplateHole { id: 0, category: Some(CategoryId(0)) }],
                Some(CategoryId(0)),
            )
            .expect("root hole");
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].production, None);
        assert_eq!(parsed[0].syntax, parsed[0].value);
        assert_eq!(parsed[0].value, DynamicValue::TemplateHole { id: 0, category: CategoryId(0) });
    }

    #[test]
    fn text_tokens_cannot_span_a_structural_hole() {
        let (mut grammar, mut image) = integer_grammar();
        grammar.categories[0].admits_variables = true;
        image.core_fingerprint = grammar.fingerprint().expect("fingerprint");
        let host = DefaultRuntimeHost;
        let parser = RuntimeParser::new(&grammar, &image, "test", "test", &host).expect("parser");
        let result = parser.parse_template(
            &[
                RuntimeTemplatePiece::Text("1".into()),
                RuntimeTemplatePiece::Hole(0),
                RuntimeTemplatePiece::Text("2".into()),
            ],
            &[RuntimeTemplateHole { id: 0, category: None }],
            Some(CategoryId(0)),
        );
        assert!(matches!(result, Err(RuntimeError::NoParse)));
    }

    #[test]
    fn structural_template_extent_is_bounded_before_occurrence_allocation() {
        let (mut grammar, mut image) = integer_grammar();
        grammar.categories[0].admits_variables = true;
        image.core_fingerprint = grammar.fingerprint().expect("fingerprint");
        let policy = RuntimePolicy {
            max_input_bytes: 2,
            max_capture_bindings: 1,
            ..RuntimePolicy::default()
        };
        let parser = RuntimeParser::new_with_policy(
            &grammar,
            &image,
            "test",
            "test",
            &DefaultRuntimeHost,
            policy,
        )
        .expect("bounded parser");

        let too_many_pieces = parser.parse_template(
            &[
                RuntimeTemplatePiece::Hole(0),
                RuntimeTemplatePiece::Hole(0),
                RuntimeTemplatePiece::Hole(0),
            ],
            &[RuntimeTemplateHole { id: 0, category: None }],
            Some(CategoryId(0)),
        );
        assert!(matches!(too_many_pieces, Err(RuntimeError::InputTooLarge)));

        let too_many_declarations = parser.parse_template(
            &[RuntimeTemplatePiece::Hole(0), RuntimeTemplatePiece::Hole(1)],
            &[
                RuntimeTemplateHole { id: 0, category: None },
                RuntimeTemplateHole { id: 1, category: None },
            ],
            Some(CategoryId(0)),
        );
        assert!(matches!(
            too_many_declarations,
            Err(RuntimeError::InvalidTemplate("hole declaration limit exceeded"))
        ));
    }

    #[test]
    fn empty_text_piece_is_not_a_canonical_structural_fragment() {
        let (grammar, image) = integer_grammar();
        let parser = RuntimeParser::new(&grammar, &image, "test", "test", &DefaultRuntimeHost)
            .expect("parser");
        let result = parser.parse_template(
            &[RuntimeTemplatePiece::Text(String::new())],
            &[],
            Some(CategoryId(0)),
        );
        assert!(matches!(
            result,
            Err(RuntimeError::InvalidTemplate("text pieces must be nonempty"))
        ));
    }
}
