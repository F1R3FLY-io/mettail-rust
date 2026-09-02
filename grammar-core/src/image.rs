use crate::{
    CollectionKind, ExactParseCost, GrammarCoreV1, GrammarLimits, ProductionId, ReductionPlan,
    TokenId,
};
use regex_automata::{
    dfa::{dense, Automaton, StartKind},
    Anchored,
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub const PARSER_IMAGE_MAGIC: [u8; 8] = *b"MTILIMG1";
pub const PARSER_IMAGE_ABI_V1: u16 = 1;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ParserImageV1 {
    pub magic: [u8; 8],
    pub abi: u16,
    pub compiler_abi: String,
    pub unicode_version: String,
    pub core_fingerprint: [u8; 32],
    pub kind: ParserImageKind,
    pub index_width: IndexWidth,
    pub exact: bool,
    pub lexer: LexerImage,
    pub reductions: Vec<ReductionPlan>,
    pub engine: EngineTables,
    pub limits: GrammarLimits,
}

impl ParserImageV1 {
    /// Construct a non-executable image header for tooling and registry
    /// negotiation. This must never be installed as a parser.
    pub fn metadata_only(
        core: &GrammarCoreV1,
        compiler_abi: impl Into<String>,
        unicode_version: impl Into<String>,
    ) -> Result<Self, ImageBuildError> {
        core.validate().map_err(ImageBuildError::InvalidGrammar)?;
        if !core.weight_profile.is_consensus_safe() {
            return Err(ImageBuildError::NonExactProfile);
        }
        let index_width = IndexWidth::for_max(
            core.categories
                .len()
                .max(core.tokens.len())
                .max(core.productions.len()),
        );
        Ok(Self {
            magic: PARSER_IMAGE_MAGIC,
            abi: PARSER_IMAGE_ABI_V1,
            compiler_abi: compiler_abi.into(),
            unicode_version: unicode_version.into(),
            core_fingerprint: core.fingerprint().map_err(ImageBuildError::Encode)?,
            kind: ParserImageKind::MetadataOnly,
            index_width,
            exact: true,
            lexer: LexerImage::default(),
            reductions: core.reductions.clone(),
            engine: EngineTables::default(),
            limits: core.limits,
        })
    }

    pub fn encode(&self) -> Result<Vec<u8>, postcard::Error> {
        postcard::to_allocvec(self)
    }

    pub fn decode_verified(bytes: &[u8], expected_core: [u8; 32]) -> Result<Self, ImageError> {
        let image: Self = postcard::from_bytes(bytes).map_err(ImageError::Decode)?;
        image.verify(expected_core)?;
        Ok(image)
    }

    /// Decode an executable cache image and verify every field that is derived
    /// from, or selected for, the authoritative grammar.
    pub fn decode_executable_verified(
        bytes: &[u8],
        core: &GrammarCoreV1,
        compiler_abi: &str,
        unicode_version: &str,
    ) -> Result<Self, ImageError> {
        Self::decode_executable_verified_with_limits(
            bytes,
            core,
            compiler_abi,
            unicode_version,
            ParserImageAdmissionLimits::default(),
        )
    }

    pub fn decode_executable_verified_with_limits(
        bytes: &[u8],
        core: &GrammarCoreV1,
        compiler_abi: &str,
        unicode_version: &str,
        limits: ParserImageAdmissionLimits,
    ) -> Result<Self, ImageError> {
        if bytes.len() > limits.max_encoded_bytes {
            return Err(ImageError::ImageLimitExceeded("encoded bytes"));
        }
        let image: Self = postcard::from_bytes(bytes).map_err(ImageError::Decode)?;
        image.verify_executable_with_limits(core, compiler_abi, unicode_version, limits)?;
        Ok(image)
    }

    pub fn verify(&self, expected_core: [u8; 32]) -> Result<(), ImageError> {
        if self.magic != PARSER_IMAGE_MAGIC {
            return Err(ImageError::BadMagic);
        }
        if self.abi != PARSER_IMAGE_ABI_V1 {
            return Err(ImageError::UnsupportedAbi(self.abi));
        }
        if self.core_fingerprint != expected_core {
            return Err(ImageError::CoreFingerprintMismatch);
        }
        if !self.exact {
            return Err(ImageError::NonExactImage);
        }
        self.lexer.verify()?;
        Ok(())
    }

    pub fn verify_executable(
        &self,
        core: &GrammarCoreV1,
        compiler_abi: &str,
        unicode_version: &str,
    ) -> Result<(), ImageError> {
        self.verify_executable_with_limits(
            core,
            compiler_abi,
            unicode_version,
            ParserImageAdmissionLimits::default(),
        )
    }

    pub fn verify_executable_with_limits(
        &self,
        core: &GrammarCoreV1,
        compiler_abi: &str,
        unicode_version: &str,
        limits: ParserImageAdmissionLimits,
    ) -> Result<(), ImageError> {
        core.validate().map_err(ImageError::InvalidGrammar)?;
        let fingerprint = core.fingerprint().map_err(ImageError::EncodeCore)?;
        self.verify(fingerprint)?;
        if self.kind != ParserImageKind::Executable {
            return Err(ImageError::NotExecutable);
        }
        if self.compiler_abi != compiler_abi {
            return Err(ImageError::CompilerAbiMismatch);
        }
        if self.unicode_version != unicode_version {
            return Err(ImageError::UnicodeVersionMismatch);
        }
        if self.limits != core.limits {
            return Err(ImageError::LimitsMismatch);
        }
        if self.reductions != core.reductions {
            return Err(ImageError::ReductionsMismatch);
        }
        let expected_width = IndexWidth::for_max(
            core.categories
                .len()
                .max(core.tokens.len())
                .max(core.productions.len())
                .max(self.engine.nonterminal_count as usize),
        );
        if self.index_width != expected_width {
            return Err(ImageError::IndexWidthMismatch);
        }
        limits.verify(self)?;
        self.verify_lexer_references(core)?;
        self.verify_lexer_languages(core)?;
        self.engine.verify(core)?;
        Ok(())
    }

    fn verify_lexer_references(&self, core: &GrammarCoreV1) -> Result<(), ImageError> {
        if self.lexer.mode_starts.len() != core.modes.len() {
            return Err(ImageError::LexerModeCountMismatch);
        }
        if self.lexer.states.is_empty() {
            return Err(ImageError::EmptyExecutableLexer);
        }
        let mut owners = vec![None; self.lexer.states.len()];
        for (mode_index, start) in self.lexer.mode_starts.iter().copied().enumerate() {
            if start as usize >= self.lexer.states.len() {
                return Err(ImageError::BadLexerState(start));
            }
            if !self.lexer.states[start as usize].accept.is_empty() {
                return Err(ImageError::NullableLexerMode(mode_index as u32));
            }
            let mut queue = VecDeque::from([start]);
            while let Some(state_index) = queue.pop_front() {
                match owners[state_index as usize] {
                    Some(owner) if owner != mode_index as u32 => {
                        return Err(ImageError::SharedLexerState(state_index));
                    },
                    Some(_) => continue,
                    None => owners[state_index as usize] = Some(mode_index as u32),
                }
                let state = &self.lexer.states[state_index as usize];
                let mut previous = None;
                for token in &state.accept {
                    let Some(definition) = core.tokens.get(token.0 as usize) else {
                        return Err(ImageError::BadLexerToken(token.0));
                    };
                    if definition.mode.0 != mode_index as u32 {
                        return Err(ImageError::LexerModeOwnership {
                            state: state_index,
                            token: token.0,
                        });
                    }
                    let key = (std::cmp::Reverse(definition.priority), definition.id);
                    if previous.is_some_and(|previous| previous >= key) {
                        return Err(ImageError::NonCanonicalLexerAccepts(state_index));
                    }
                    previous = Some(key);
                }
                if let Some(primary) = state.accept.first() {
                    let primary = &core.tokens[primary.0 as usize];
                    for candidate in state.accept.iter().skip(1) {
                        let candidate = &core.tokens[candidate.0 as usize];
                        if candidate.transition != primary.transition
                            || candidate.channel != primary.channel
                        {
                            return Err(ImageError::IncompatibleLexerAccepts(state_index));
                        }
                    }
                }
                let transition_start = state.transition_start as usize;
                let transition_end = transition_start + state.transition_len as usize;
                queue.extend(
                    self.lexer.transitions[transition_start..transition_end]
                        .iter()
                        .map(|transition| transition.target),
                );
            }
        }
        if let Some((state, _)) = owners.iter().enumerate().find(|(_, owner)| owner.is_none()) {
            return Err(ImageError::UnreachableLexerState(state as u32));
        }
        for state in &self.lexer.states {
            for token in &state.accept {
                if token.0 as usize >= core.tokens.len() {
                    return Err(ImageError::BadLexerToken(token.0));
                }
            }
        }
        Ok(())
    }

    fn verify_lexer_languages(&self, core: &GrammarCoreV1) -> Result<(), ImageError> {
        for mode in &core.modes {
            let actual_start = self.lexer.mode_starts[mode.id.0 as usize];
            for token_id in &mode.token_ids {
                let token = &core.tokens[token_id.0 as usize];
                let source = match &token.pattern {
                    crate::TokenPattern::Literal(text) => regex_syntax::escape(text),
                    crate::TokenPattern::Regex(pattern) => pattern.clone(),
                    crate::TokenPattern::Builtin(crate::BuiltinToken::EndOfInput) => {
                        if self
                            .lexer
                            .states
                            .iter()
                            .any(|state| state.accept.contains(token_id))
                        {
                            return Err(ImageError::EndOfInputLexerAccept(token_id.0));
                        }
                        continue;
                    },
                    crate::TokenPattern::Builtin(builtin) => crate::builtin_token_pattern(*builtin)
                        .expect("non-EOI builtin has a canonical pattern")
                        .into(),
                };
                let full_match = format!(r"(?:{source})\z");
                let expected = dense::Builder::new()
                    .configure(dense::Config::new().start_kind(StartKind::Anchored))
                    .build(&full_match)
                    .map_err(|error| ImageError::LexerPattern {
                        token: token_id.0,
                        message: error.to_string(),
                    })?;
                let expected_start =
                    expected
                        .universal_start_state(Anchored::Yes)
                        .ok_or_else(|| ImageError::LexerPattern {
                            token: token_id.0,
                            message: "pattern has no context-independent anchored start state"
                                .into(),
                        })?;
                let mut queue = VecDeque::from([(Some(actual_start), expected_start)]);
                let mut seen = BTreeSet::new();
                while let Some((actual_state, expected_state)) = queue.pop_front() {
                    if !seen.insert((actual_state, expected_state.as_usize())) {
                        continue;
                    }
                    let actual_accepts = actual_state.is_some_and(|state| {
                        self.lexer.states[state as usize].accept.contains(token_id)
                    });
                    let expected_accepts =
                        expected.is_match_state(expected.next_eoi_state(expected_state));
                    if actual_accepts != expected_accepts {
                        return Err(ImageError::LexerLanguageMismatch(token_id.0));
                    }
                    for byte in u8::MIN..=u8::MAX {
                        let actual_next = actual_state
                            .and_then(|state| lexer_image_transition(&self.lexer, state, byte));
                        let expected_next = expected.next_state(expected_state, byte);
                        let key = (actual_next, expected_next.as_usize());
                        if !seen.contains(&key) {
                            queue.push_back((actual_next, expected_next));
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParserImageAdmissionLimits {
    pub max_encoded_bytes: usize,
    pub max_lexer_states: usize,
    pub max_lexer_transitions: usize,
    pub max_nonterminals: u32,
    pub max_runtime_rules: usize,
    pub max_runtime_symbols: usize,
}

impl Default for ParserImageAdmissionLimits {
    fn default() -> Self {
        Self {
            max_encoded_bytes: 256 * 1024 * 1024,
            max_lexer_states: 4_000_000,
            max_lexer_transitions: 64_000_000,
            max_nonterminals: 4_000_000,
            max_runtime_rules: 4_000_000,
            max_runtime_symbols: 64_000_000,
        }
    }
}

impl ParserImageAdmissionLimits {
    fn verify(self, image: &ParserImageV1) -> Result<(), ImageError> {
        for (exceeded, name) in [
            (image.lexer.states.len() > self.max_lexer_states, "lexer states"),
            (image.lexer.transitions.len() > self.max_lexer_transitions, "lexer transitions"),
            (image.engine.nonterminal_count > self.max_nonterminals, "nonterminals"),
            (image.engine.runtime_rules.len() > self.max_runtime_rules, "runtime rules"),
            (image.engine.runtime_symbols.len() > self.max_runtime_symbols, "runtime symbols"),
        ] {
            if exceeded {
                return Err(ImageError::ImageLimitExceeded(name));
            }
        }
        Ok(())
    }
}

fn lexer_image_transition(lexer: &LexerImage, state: u32, byte: u8) -> Option<u32> {
    let state = lexer.states.get(state as usize)?;
    let start = state.transition_start as usize;
    let end = start.checked_add(state.transition_len as usize)?;
    lexer
        .transitions
        .get(start..end)?
        .iter()
        .find_map(|transition| {
            (transition.start <= byte && byte <= transition.end).then_some(transition.target)
        })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ParserImageKind {
    MetadataOnly,
    Executable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum IndexWidth {
    U8,
    U16,
    U32,
}

impl IndexWidth {
    pub fn for_max(max: usize) -> Self {
        if max <= u8::MAX as usize {
            Self::U8
        } else if max <= u16::MAX as usize {
            Self::U16
        } else {
            Self::U32
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexerImage {
    pub mode_starts: Vec<u32>,
    pub states: Vec<LexerState>,
    pub transitions: Vec<LexerTransition>,
}

impl LexerImage {
    fn verify(&self) -> Result<(), ImageError> {
        for start in &self.mode_starts {
            if *start as usize >= self.states.len() {
                return Err(ImageError::BadLexerState(*start));
            }
        }
        for (state_index, state) in self.states.iter().enumerate() {
            let start = state.transition_start as usize;
            let end = start
                .checked_add(state.transition_len as usize)
                .ok_or(ImageError::BadLexerTransitionSlice(state_index as u32))?;
            let transitions = self
                .transitions
                .get(start..end)
                .ok_or(ImageError::BadLexerTransitionSlice(state_index as u32))?;
            let mut previous_end = None;
            for transition in transitions {
                if transition.target as usize >= self.states.len() {
                    return Err(ImageError::BadLexerState(transition.target));
                }
                if transition.start > transition.end {
                    return Err(ImageError::BadCharacterRange);
                }
                if previous_end.is_some_and(|value| value >= transition.start) {
                    return Err(ImageError::OverlappingLexerTransitions(state_index as u32));
                }
                previous_end = Some(transition.end);
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexerState {
    pub transition_start: u32,
    pub transition_len: u32,
    pub accept: Vec<TokenId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexerTransition {
    pub start: u8,
    pub end: u8,
    pub target: u32,
}

/// Tables for non-step queries made by the generalized WPDA walker.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineTables {
    pub nonterminal_count: u32,
    pub start_nonterminals: Vec<u32>,
    pub nonterminal_rule_starts: Vec<u32>,
    pub runtime_rules: Vec<RuntimeRule>,
    pub runtime_symbols: Vec<RuntimeSymbol>,
    pub same_span_ranks: Vec<u32>,
    pub chain_atoms: Vec<ChainAtomEntry>,
    pub non_atom_prefixes: Vec<TokenSetEntry>,
    pub parikh_classes: Vec<Option<u8>>,
    pub parikh_must_masks: Vec<ParikhMaskEntry>,
    pub collection_rules: Vec<CollectionRuleEntry>,
    pub category_min_spans: Vec<u16>,
    pub coercions: Vec<CoercionEntry>,
    pub operator_floors: Vec<OperatorFloorEntry>,
    pub structural_open_tokens: Vec<TokenId>,
    pub structural_close_tokens: Vec<TokenId>,
}

impl EngineTables {
    fn verify(&self, core: &GrammarCoreV1) -> Result<(), ImageError> {
        if self.nonterminal_count < core.categories.len() as u32 {
            return Err(ImageError::BadNonterminalCount);
        }
        if self.nonterminal_rule_starts.len() != self.nonterminal_count as usize + 1 {
            return Err(ImageError::BadNonterminalRuleIndex);
        }
        if self.nonterminal_rule_starts.first().copied() != Some(0)
            || self.nonterminal_rule_starts.last().copied() != Some(self.runtime_rules.len() as u32)
            || self
                .nonterminal_rule_starts
                .windows(2)
                .any(|pair| pair[0] > pair[1])
        {
            return Err(ImageError::BadNonterminalRuleIndex);
        }
        for start in &self.start_nonterminals {
            if *start as usize >= core.categories.len() {
                return Err(ImageError::BadStartNonterminal(*start));
            }
        }
        if !core.productions.is_empty() && self.runtime_rules.is_empty() {
            return Err(ImageError::MissingRuntimeRules);
        }

        let mut nonterminal_output_arities = vec![None; self.nonterminal_count as usize];
        for output in nonterminal_output_arities
            .iter_mut()
            .take(core.categories.len())
        {
            *output = Some(1u16);
        }
        for rule in &self.runtime_rules {
            if rule.lhs >= self.nonterminal_count {
                return Err(ImageError::BadRuleNonterminal(rule.lhs));
            }
            let actual = rule.semantic.output_arity();
            let output = &mut nonterminal_output_arities[rule.lhs as usize];
            match *output {
                Some(expected) if expected != actual => {
                    return Err(ImageError::RuntimeOutputArityMismatch {
                        nonterminal: rule.lhs,
                        expected: u32::from(expected),
                        actual: u32::from(actual),
                    });
                },
                Some(_) => {},
                None => *output = Some(actual),
            }
        }

        let mut production_counts = vec![0u32; core.productions.len()];
        let mut foreign_delimiters = BTreeMap::new();
        for (index, rule) in self.runtime_rules.iter().enumerate() {
            if rule.lhs >= self.nonterminal_count {
                return Err(ImageError::BadRuleNonterminal(index as u32));
            }
            let symbol_start = rule.symbol_start as usize;
            let symbol_end = symbol_start
                .checked_add(rule.symbol_len as usize)
                .ok_or(ImageError::BadRuleSymbolSlice(index as u32))?;
            let symbols = self
                .runtime_symbols
                .get(symbol_start..symbol_end)
                .ok_or(ImageError::BadRuleSymbolSlice(index as u32))?;
            for symbol in symbols {
                match symbol {
                    RuntimeSymbol::Token { token, .. } => {
                        if token.0 as usize >= core.tokens.len() {
                            return Err(ImageError::BadRuntimeToken(token.0));
                        }
                    },
                    RuntimeSymbol::Nonterminal { nonterminal, .. } => {
                        if *nonterminal >= self.nonterminal_count {
                            return Err(ImageError::BadRuntimeNonterminal(*nonterminal));
                        }
                    },
                    RuntimeSymbol::Foreign { open, close, .. } => {
                        if open.is_empty() || close.is_empty() || open == close {
                            return Err(ImageError::EmptyForeignDelimiter(index as u32));
                        }
                        if let Some(previous) =
                            foreign_delimiters.insert(open.clone(), close.clone())
                        {
                            if previous != *close {
                                return Err(ImageError::AmbiguousForeignDelimiter(open.clone()));
                            }
                        }
                    },
                }
            }
            let mut captures = 0usize;
            for symbol in symbols {
                let width = match symbol {
                    RuntimeSymbol::Token { capture: true, .. }
                    | RuntimeSymbol::Foreign { capture: true, .. } => 1usize,
                    RuntimeSymbol::Nonterminal { nonterminal, capture: true } => usize::from(
                        nonterminal_output_arities[*nonterminal as usize]
                            .ok_or(ImageError::MissingRuntimeOutputArity(*nonterminal))?,
                    ),
                    RuntimeSymbol::Token { capture: false, .. }
                    | RuntimeSymbol::Nonterminal { capture: false, .. }
                    | RuntimeSymbol::Foreign { capture: false, .. } => 0,
                };
                captures = captures
                    .checked_add(width)
                    .ok_or(ImageError::RuntimeCaptureArityOverflow(index as u32))?;
            }
            match (&rule.production, &rule.semantic) {
                (Some(production), RuntimeRuleSemantic::Reduce) => {
                    let Some(core_production) = core.productions.get(production.0 as usize) else {
                        return Err(ImageError::BadRuntimeProduction(production.0));
                    };
                    if core_production.result.0 != rule.lhs {
                        return Err(ImageError::RuntimeProductionResultMismatch(production.0));
                    }
                    let reduction = &core.reductions[core_production.reduction as usize];
                    if captures != reduction.input_arity as usize {
                        return Err(ImageError::RuntimeCaptureArity {
                            rule: index as u32,
                            expected: u32::from(reduction.input_arity),
                            actual: captures as u32,
                        });
                    }
                    production_counts[production.0 as usize] += 1;
                },
                (None, RuntimeRuleSemantic::Reduce) | (Some(_), _) => {
                    return Err(ImageError::BadRuntimeSemantic(index as u32));
                },
                (None, _) => {},
            }
            let expected_auxiliary = match rule.semantic {
                RuntimeRuleSemantic::Reduce => None,
                RuntimeRuleSemantic::EmptyOptional { .. }
                | RuntimeRuleSemantic::EmptyCollection { .. }
                | RuntimeRuleSemantic::Unit { .. } => Some(0usize),
                RuntimeRuleSemantic::PresentOptional { slots } => Some(slots as usize),
                RuntimeRuleSemantic::SingletonCollection { layout } => {
                    Some(layout.slots() as usize)
                },
                RuntimeRuleSemantic::AppendCollection { layout } => {
                    Some(layout.slots() as usize * 2)
                },
                RuntimeRuleSemantic::FinalizeCollection { layout } => Some(layout.slots() as usize),
                RuntimeRuleSemantic::Tuple { slots } => Some(slots as usize),
            };
            if let Some(expected) = expected_auxiliary {
                if captures != expected {
                    return Err(ImageError::RuntimeCaptureArity {
                        rule: index as u32,
                        expected: expected as u32,
                        actual: captures as u32,
                    });
                }
            }
        }
        if production_counts.iter().any(|count| *count != 1) {
            return Err(ImageError::RuntimeProductionCoverage);
        }
        for nonterminal in 0..self.nonterminal_count as usize {
            let start = self.nonterminal_rule_starts[nonterminal] as usize;
            let end = self.nonterminal_rule_starts[nonterminal + 1] as usize;
            if self.runtime_rules[start..end]
                .iter()
                .any(|rule| rule.lhs as usize != nonterminal)
            {
                return Err(ImageError::BadNonterminalRuleIndex);
            }
        }
        let analysis = derive_runtime_analysis(self).map_err(ImageError::RuntimeAnalysis)?;
        if self.same_span_ranks != analysis.same_span_ranks {
            return Err(ImageError::SameSpanRankMismatch);
        }
        if self.category_min_spans != analysis.nonterminal_min_spans[..core.categories.len()] {
            return Err(ImageError::CategoryMinSpanMismatch);
        }
        for token in self
            .structural_open_tokens
            .iter()
            .chain(&self.structural_close_tokens)
        {
            if token.0 as usize >= core.tokens.len() {
                return Err(ImageError::BadRuntimeToken(token.0));
            }
        }
        let normalized =
            crate::normalize_runtime_engine(core).map_err(ImageError::EngineNormalization)?;
        if self != &normalized {
            return Err(ImageError::NonCanonicalEngine);
        }
        Ok(())
    }

    pub fn rules_for(&self, nonterminal: u32) -> &[RuntimeRule] {
        let Some(bounds) = self
            .nonterminal_rule_starts
            .get(nonterminal as usize..=nonterminal as usize + 1)
        else {
            return &[];
        };
        &self.runtime_rules[bounds[0] as usize..bounds[1] as usize]
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeRule {
    pub lhs: u32,
    pub symbol_start: u32,
    pub symbol_len: u16,
    pub production: Option<ProductionId>,
    pub semantic: RuntimeRuleSemantic,
    pub cost: ExactParseCost,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeSymbol {
    Token {
        token: TokenId,
        capture: bool,
    },
    Nonterminal {
        nonterminal: u32,
        capture: bool,
    },
    Foreign {
        open: String,
        close: String,
        capture: bool,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeRuleSemantic {
    Reduce,
    EmptyOptional { slots: u16 },
    PresentOptional { slots: u16 },
    EmptyCollection { layout: RuntimeCollectionLayout },
    SingletonCollection { layout: RuntimeCollectionLayout },
    AppendCollection { layout: RuntimeCollectionLayout },
    FinalizeCollection { layout: RuntimeCollectionLayout },
    Tuple { slots: u16 },
    Unit { slots: u16 },
}

impl RuntimeRuleSemantic {
    pub fn output_arity(self) -> u16 {
        match self {
            Self::Reduce | Self::Tuple { .. } => 1,
            Self::EmptyOptional { slots }
            | Self::PresentOptional { slots }
            | Self::Unit { slots } => slots,
            Self::EmptyCollection { layout }
            | Self::SingletonCollection { layout }
            | Self::AppendCollection { layout }
            | Self::FinalizeCollection { layout } => layout.slots(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeCollectionLayout {
    Uniform {
        slots: u16,
        kind: CollectionKind,
    },
    Pair {
        left: CollectionKind,
        right: CollectionKind,
    },
}

impl RuntimeCollectionLayout {
    pub fn slots(self) -> u16 {
        match self {
            Self::Uniform { slots, .. } => slots,
            Self::Pair { .. } => 2,
        }
    }

    pub fn kind(self, index: usize) -> Option<CollectionKind> {
        match self {
            Self::Uniform { slots, kind } => (index < slots as usize).then_some(kind),
            Self::Pair { left, .. } if index == 0 => Some(left),
            Self::Pair { right, .. } if index == 1 => Some(right),
            Self::Pair { .. } => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChainAtomEntry {
    pub category: u32,
    pub token: TokenId,
    pub productions: Vec<ProductionId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TokenSetEntry {
    pub category: u32,
    pub tokens: Vec<TokenId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParikhMaskEntry {
    pub category: u32,
    pub production: u32,
    pub position: u16,
    pub mask: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollectionRuleEntry {
    pub production: ProductionId,
    pub element_category: u32,
    pub separator: String,
    pub key_value_separator: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoercionEntry {
    pub source: u32,
    pub target: u32,
    pub production: ProductionId,
    pub cost: ExactParseCost,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperatorFloorEntry {
    pub category: u32,
    pub token: TokenId,
    pub minimum_binding_power: u16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuntimeAnalysis {
    pub same_span_ranks: Vec<u32>,
    pub nonterminal_min_spans: Vec<u16>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeAnalysisError {
    BadRuleSymbolSlice(u32),
    BadNonterminal(u32),
    NonContractingCycle,
    RankOverflow,
}

pub fn derive_runtime_analysis(
    engine: &EngineTables,
) -> Result<RuntimeAnalysis, RuntimeAnalysisError> {
    let count = engine.nonterminal_count as usize;
    let mut nullable = vec![false; count];
    loop {
        let mut changed = false;
        for (index, rule) in engine.runtime_rules.iter().enumerate() {
            let lhs = rule.lhs as usize;
            if lhs >= count {
                return Err(RuntimeAnalysisError::BadNonterminal(rule.lhs));
            }
            let start = rule.symbol_start as usize;
            let end = start
                .checked_add(rule.symbol_len as usize)
                .ok_or(RuntimeAnalysisError::BadRuleSymbolSlice(index as u32))?;
            let symbols = engine
                .runtime_symbols
                .get(start..end)
                .ok_or(RuntimeAnalysisError::BadRuleSymbolSlice(index as u32))?;
            let rule_nullable = symbols.iter().all(|symbol| match symbol {
                RuntimeSymbol::Nonterminal { nonterminal, .. } => nullable
                    .get(*nonterminal as usize)
                    .copied()
                    .unwrap_or(false),
                RuntimeSymbol::Token { .. } | RuntimeSymbol::Foreign { .. } => false,
            });
            if rule_nullable && !nullable[lhs] {
                nullable[lhs] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut children = vec![BTreeSet::new(); count];
    let mut parents = vec![BTreeSet::new(); count];
    for (index, rule) in engine.runtime_rules.iter().enumerate() {
        let start = rule.symbol_start as usize;
        let end = start
            .checked_add(rule.symbol_len as usize)
            .ok_or(RuntimeAnalysisError::BadRuleSymbolSlice(index as u32))?;
        let symbols = engine
            .runtime_symbols
            .get(start..end)
            .ok_or(RuntimeAnalysisError::BadRuleSymbolSlice(index as u32))?;
        for (position, symbol) in symbols.iter().enumerate() {
            let RuntimeSymbol::Nonterminal { nonterminal, .. } = symbol else {
                continue;
            };
            if *nonterminal as usize >= count {
                return Err(RuntimeAnalysisError::BadNonterminal(*nonterminal));
            }
            let other_symbols_nullable = symbols.iter().enumerate().all(|(other, symbol)| {
                position == other
                    || match symbol {
                        RuntimeSymbol::Nonterminal { nonterminal, .. } => {
                            nullable[*nonterminal as usize]
                        },
                        RuntimeSymbol::Token { .. } | RuntimeSymbol::Foreign { .. } => false,
                    }
            });
            if other_symbols_nullable {
                children[rule.lhs as usize].insert(*nonterminal as usize);
                parents[*nonterminal as usize].insert(rule.lhs as usize);
            }
        }
    }

    let mut remaining: Vec<_> = children.iter().map(BTreeSet::len).collect();
    let mut queue: VecDeque<_> = remaining
        .iter()
        .enumerate()
        .filter_map(|(index, degree)| (*degree == 0).then_some(index))
        .collect();
    let mut ranks = vec![0u32; count];
    let mut processed = 0usize;
    while let Some(child) = queue.pop_front() {
        processed += 1;
        for parent in parents[child].iter().copied() {
            ranks[parent] = ranks[parent].max(
                ranks[child]
                    .checked_add(1)
                    .ok_or(RuntimeAnalysisError::RankOverflow)?,
            );
            remaining[parent] -= 1;
            if remaining[parent] == 0 {
                queue.push_back(parent);
            }
        }
    }
    if processed != count {
        return Err(RuntimeAnalysisError::NonContractingCycle);
    }

    let mut minimum = vec![u32::MAX; count];
    loop {
        let mut changed = false;
        for (index, rule) in engine.runtime_rules.iter().enumerate() {
            let start = rule.symbol_start as usize;
            let end = start
                .checked_add(rule.symbol_len as usize)
                .ok_or(RuntimeAnalysisError::BadRuleSymbolSlice(index as u32))?;
            let symbols = engine
                .runtime_symbols
                .get(start..end)
                .ok_or(RuntimeAnalysisError::BadRuleSymbolSlice(index as u32))?;
            let mut span = 0u32;
            let mut productive = true;
            for symbol in symbols {
                match symbol {
                    RuntimeSymbol::Token { .. } | RuntimeSymbol::Foreign { .. } => {
                        span = span.saturating_add(1);
                    },
                    RuntimeSymbol::Nonterminal { nonterminal, .. } => {
                        let child = minimum[*nonterminal as usize];
                        if child == u32::MAX {
                            productive = false;
                            break;
                        }
                        span = span.saturating_add(child);
                    },
                }
            }
            let lhs = rule.lhs as usize;
            if productive && span < minimum[lhs] {
                minimum[lhs] = span;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    Ok(RuntimeAnalysis {
        same_span_ranks: ranks,
        nonterminal_min_spans: minimum
            .into_iter()
            .map(|value| value.min(u16::MAX as u32) as u16)
            .collect(),
    })
}

#[derive(Debug)]
pub enum ImageBuildError {
    InvalidGrammar(Vec<crate::ValidationError>),
    NonExactProfile,
    Encode(postcard::Error),
}

#[derive(Debug)]
pub enum ImageError {
    Decode(postcard::Error),
    EncodeCore(postcard::Error),
    InvalidGrammar(Vec<crate::ValidationError>),
    BadMagic,
    UnsupportedAbi(u16),
    CoreFingerprintMismatch,
    NonExactImage,
    NotExecutable,
    CompilerAbiMismatch,
    UnicodeVersionMismatch,
    LimitsMismatch,
    ReductionsMismatch,
    IndexWidthMismatch,
    MissingRuntimeRules,
    EmptyExecutableLexer,
    BadLexerState(u32),
    BadLexerToken(u32),
    BadLexerTransitionSlice(u32),
    OverlappingLexerTransitions(u32),
    BadCharacterRange,
    LexerModeCountMismatch,
    NullableLexerMode(u32),
    SharedLexerState(u32),
    UnreachableLexerState(u32),
    LexerModeOwnership {
        state: u32,
        token: u32,
    },
    NonCanonicalLexerAccepts(u32),
    IncompatibleLexerAccepts(u32),
    EndOfInputLexerAccept(u32),
    LexerPattern {
        token: u32,
        message: String,
    },
    LexerLanguageMismatch(u32),
    BadNonterminalCount,
    BadStartNonterminal(u32),
    BadNonterminalRuleIndex,
    BadRuleNonterminal(u32),
    BadRuleSymbolSlice(u32),
    BadRuntimeToken(u32),
    BadRuntimeNonterminal(u32),
    BadRuntimeProduction(u32),
    RuntimeProductionResultMismatch(u32),
    RuntimeProductionCoverage,
    BadRuntimeSemantic(u32),
    EmptyForeignDelimiter(u32),
    AmbiguousForeignDelimiter(String),
    RuntimeCaptureArity {
        rule: u32,
        expected: u32,
        actual: u32,
    },
    RuntimeCaptureArityOverflow(u32),
    MissingRuntimeOutputArity(u32),
    RuntimeOutputArityMismatch {
        nonterminal: u32,
        expected: u32,
        actual: u32,
    },
    RuntimeAnalysis(RuntimeAnalysisError),
    SameSpanRankMismatch,
    CategoryMinSpanMismatch,
    EngineNormalization(crate::EngineNormalizationError),
    NonCanonicalEngine,
    ImageLimitExceeded(&'static str),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Carrier, Category, CategoryId};

    #[test]
    fn parser_image_rejects_a_different_grammar() {
        let mut core = GrammarCoreV1::new("A");
        core.categories.push(Category {
            id: CategoryId(0),
            name: "Term".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        let image =
            ParserImageV1::metadata_only(&core, "test", "15.1").expect("valid image metadata");
        let mut other = core.clone();
        other.name = "B".into();
        assert!(matches!(
            image.verify(other.fingerprint().expect("fingerprint")),
            Err(ImageError::CoreFingerprintMismatch)
        ));
    }

    #[test]
    fn metadata_image_is_never_executable() {
        let mut core = GrammarCoreV1::new("A");
        core.categories.push(Category {
            id: CategoryId(0),
            name: "Term".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        let image =
            ParserImageV1::metadata_only(&core, "test", "15.1").expect("valid image metadata");
        assert!(matches!(
            image.verify_executable(&core, "test", "15.1"),
            Err(ImageError::NotExecutable)
        ));
    }
}
