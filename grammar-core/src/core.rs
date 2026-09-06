use crate::{CanonicalValue, NativeEvaluation, ReductionPlan, SemanticProgram, WeightProfile};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

macro_rules! id_type {
    ($name:ident) => {
        #[derive(
            Clone,
            Copy,
            Debug,
            Default,
            PartialEq,
            Eq,
            PartialOrd,
            Ord,
            Hash,
            Serialize,
            Deserialize,
        )]
        pub struct $name(pub u32);
    };
}

id_type!(CategoryId);
id_type!(TokenId);
id_type!(ModeId);
id_type!(ProductionId);
id_type!(ConstructorId);

pub const GRAMMAR_CORE_ABI_V1: u16 = 1;
pub const GRAMMAR_CORE_ABI_V2: u16 = 2;
pub const GRAMMAR_CORE_ABI_CURRENT: u16 = GRAMMAR_CORE_ABI_V2;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct GrammarCoreV1 {
    pub abi: u16,
    pub name: String,
    pub backend_context: Option<String>,
    pub documentation: Option<String>,
    pub categories: Vec<Category>,
    pub tokens: Vec<TokenDefinition>,
    pub modes: Vec<LexerMode>,
    pub productions: Vec<Production>,
    pub reductions: Vec<ReductionPlan>,
    pub semantic_dependencies: Vec<Vec<ConstructorId>>,
    pub semantic_program: SemanticProgram,
    pub parser_configuration: ParserConfiguration,
    pub synchronization: Vec<SyncConstraint>,
    pub tree_invariants: Vec<TreeInvariant>,
    pub refinement_types: Vec<RefinementType>,
    pub guard_configuration: Option<GuardConfiguration>,
    pub capabilities: BTreeSet<Capability>,
    pub provenance: Provenance,
    pub limits: GrammarLimits,
    pub weight_profile: WeightProfile,
}

impl GrammarCoreV1 {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            abi: GRAMMAR_CORE_ABI_CURRENT,
            name: name.into(),
            backend_context: None,
            documentation: None,
            categories: Vec::new(),
            tokens: Vec::new(),
            modes: vec![LexerMode {
                id: ModeId(0),
                name: "default".to_string(),
                token_ids: Vec::new(),
                raw: false,
            }],
            productions: Vec::new(),
            reductions: Vec::new(),
            semantic_dependencies: Vec::new(),
            semantic_program: SemanticProgram::default(),
            parser_configuration: ParserConfiguration::default(),
            synchronization: Vec::new(),
            tree_invariants: Vec::new(),
            refinement_types: Vec::new(),
            guard_configuration: None,
            capabilities: BTreeSet::new(),
            provenance: Provenance::default(),
            limits: GrammarLimits::default(),
            weight_profile: WeightProfile::exact(),
        }
    }

    pub fn fingerprint(&self) -> Result<[u8; 32], postcard::Error> {
        // Provenance is diagnostic metadata, not language meaning. Two
        // frontends that lower the same grammar must share an identity even
        // when their source URIs, spans, or frontend names differ.
        let mut semantic = self.clone();
        semantic.backend_context = None;
        semantic.documentation = None;
        semantic.provenance = Provenance::default();
        for production in &mut semantic.productions {
            production.provenance = None;
        }
        let bytes = postcard::to_allocvec(&semantic)?;
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"mettail-grammar-core/2\0");
        hasher.update(&bytes);
        Ok(*hasher.finalize().as_bytes())
    }

    pub fn validate(&self) -> Result<(), Vec<ValidationError>> {
        let mut errors = Vec::new();
        if self.abi != GRAMMAR_CORE_ABI_CURRENT {
            errors.push(ValidationError::UnsupportedAbi(self.abi));
        }
        validate_dense_ids(&self.categories, |x| x.id.0, Entity::Category, &mut errors);
        validate_dense_ids(&self.tokens, |x| x.id.0, Entity::Token, &mut errors);
        validate_dense_ids(&self.modes, |x| x.id.0, Entity::Mode, &mut errors);
        validate_dense_ids(&self.productions, |x| x.id.0, Entity::Production, &mut errors);

        let categories = self.categories.len() as u32;
        let tokens = self.tokens.len() as u32;
        let modes = self.modes.len() as u32;
        let reductions = self.reductions.len();
        let mut names = BTreeSet::new();
        for category in &self.categories {
            if !names.insert((&category.name, Entity::Category)) {
                errors.push(ValidationError::DuplicateName(category.name.clone()));
            }
        }
        for token in &self.tokens {
            if !names.insert((&token.name, Entity::Token)) {
                errors.push(ValidationError::DuplicateName(token.name.clone()));
            }
            if token.mode.0 >= modes {
                errors.push(ValidationError::BadReference {
                    owner: Entity::Token,
                    id: token.id.0,
                    field: "mode",
                    target: token.mode.0,
                });
            }
            if let Some(next) = token.transition.push {
                if next.0 >= modes {
                    errors.push(ValidationError::BadReference {
                        owner: Entity::Token,
                        id: token.id.0,
                        field: "transition.push",
                        target: next.0,
                    });
                }
            }
            if let TokenDecoder::Capability(name) = &token.decoder {
                let capability = Capability::TokenDecoder(name.clone());
                if !self.capabilities.contains(&capability) {
                    errors.push(ValidationError::MissingCapability(capability));
                }
            }
            if let Some(category) = token.category {
                if category.0 >= categories {
                    errors.push(ValidationError::BadReference {
                        owner: Entity::Token,
                        id: token.id.0,
                        field: "category",
                        target: category.0,
                    });
                }
            }
            if let Some(evaluation) = &token.evaluation {
                validate_native_evaluation(evaluation, &self.capabilities, &mut errors);
            }
        }
        for mode in &self.modes {
            if !names.insert((&mode.name, Entity::Mode)) {
                errors.push(ValidationError::DuplicateName(mode.name.clone()));
            }
            let mut mode_tokens = BTreeSet::new();
            for token in &mode.token_ids {
                if token.0 >= tokens {
                    errors.push(ValidationError::BadReference {
                        owner: Entity::Mode,
                        id: mode.id.0,
                        field: "token_ids",
                        target: token.0,
                    });
                } else {
                    if !mode_tokens.insert(*token) {
                        errors.push(ValidationError::DuplicateReference {
                            owner: Entity::Mode,
                            id: mode.id.0,
                            field: "token_ids",
                            target: token.0,
                        });
                    }
                    if self.tokens[token.0 as usize].mode != mode.id {
                        errors.push(ValidationError::MismatchedReference {
                            owner: Entity::Mode,
                            id: mode.id.0,
                            field: "token_ids.mode",
                            target: token.0,
                        });
                    }
                }
            }
        }
        for token in &self.tokens {
            let occurrences = self
                .modes
                .iter()
                .filter(|mode| mode.token_ids.contains(&token.id))
                .count();
            if occurrences != 1 {
                errors
                    .push(ValidationError::TokenModeMembership { token: token.id.0, occurrences });
            }
        }
        for production in &self.productions {
            if production.result.0 >= categories {
                errors.push(ValidationError::BadReference {
                    owner: Entity::Production,
                    id: production.id.0,
                    field: "result",
                    target: production.result.0,
                });
            }
            validate_syntax(
                &production.syntax,
                production.id,
                categories,
                tokens,
                self.limits.max_syntax_depth,
                &mut errors,
            );
            if usize::try_from(production.reduction).map_or(true, |index| index >= reductions) {
                errors.push(ValidationError::BadReference {
                    owner: Entity::Production,
                    id: production.id.0,
                    field: "reduction",
                    target: production.reduction,
                });
            } else {
                let reduction = &self.reductions[production.reduction as usize];
                if reduction.output_category != production.result {
                    errors.push(ValidationError::MismatchedReference {
                        owner: Entity::Production,
                        id: production.id.0,
                        field: "reduction.output_category",
                        target: reduction.output_category.0,
                    });
                }
                if reduction.constructor != production.constructor {
                    errors.push(ValidationError::MismatchedReference {
                        owner: Entity::Production,
                        id: production.id.0,
                        field: "reduction.constructor",
                        target: reduction.constructor.0,
                    });
                }
                let syntax_arity = syntax_slot_count(&production.syntax);
                if syntax_arity != usize::from(reduction.input_arity) {
                    errors.push(ValidationError::ReductionSyntaxArity {
                        production: production.id.0,
                        reduction: production.reduction,
                        syntax: syntax_arity,
                        reduction_arity: reduction.input_arity,
                    });
                }
            }
        }
        for (index, reduction) in self.reductions.iter().enumerate() {
            if reduction.output_category.0 >= categories {
                errors.push(ValidationError::BadReference {
                    owner: Entity::Reduction,
                    id: index as u32,
                    field: "output_category",
                    target: reduction.output_category.0,
                });
            }
            for field in &reduction.fields {
                if let crate::FieldSource::Input(input) = field {
                    if *input >= reduction.input_arity {
                        errors.push(ValidationError::BadReductionInput {
                            reduction: index as u32,
                            input: *input,
                            arity: reduction.input_arity,
                        });
                    }
                }
            }
            if reduction.evaluation_mode.is_some() && reduction.evaluation.is_none() {
                errors.push(ValidationError::IncompleteNativeEvaluation(index as u32));
            }
            if let Some(evaluation) = &reduction.evaluation {
                validate_native_evaluation(evaluation, &self.capabilities, &mut errors);
            }
        }
        let constructors: BTreeSet<_> = self
            .productions
            .iter()
            .map(|production| production.constructor.0)
            .collect();
        for (expected, actual) in constructors.iter().copied().enumerate() {
            if actual != expected as u32 {
                errors.push(ValidationError::NonDenseId {
                    entity: Entity::Constructor,
                    expected: expected as u32,
                    actual,
                });
            }
        }
        for group in &self.semantic_dependencies {
            for constructor in group {
                if !constructors.contains(&constructor.0) {
                    errors.push(ValidationError::BadReference {
                        owner: Entity::SemanticDependency,
                        id: 0,
                        field: "constructor",
                        target: constructor.0,
                    });
                }
            }
        }
        validate_parser_configuration(&self.parser_configuration, &mut errors);
        for constraint in &self.synchronization {
            match constraint {
                SyncConstraint::Align { stream_a, stream_b, boundary_pattern } => {
                    if stream_a.is_empty() || stream_b.is_empty() || boundary_pattern.is_empty() {
                        errors.push(ValidationError::EmptySemanticName("synchronization.align"));
                    }
                },
                SyncConstraint::Track { auxiliary, primary } => {
                    if auxiliary.is_empty() || primary.is_empty() {
                        errors.push(ValidationError::EmptySemanticName("synchronization.track"));
                    }
                },
            }
        }
        let category_names: BTreeSet<_> = self
            .categories
            .iter()
            .map(|category| category.name.as_str())
            .collect();
        let production_labels: BTreeSet<_> = self
            .productions
            .iter()
            .map(|production| production.label.as_str())
            .collect();
        let mut invariant_names = BTreeSet::new();
        for invariant in &self.tree_invariants {
            if invariant.name.is_empty() {
                errors.push(ValidationError::EmptySemanticName("tree_invariant"));
            } else if !invariant_names.insert(invariant.name.as_str()) {
                errors.push(ValidationError::DuplicateName(invariant.name.clone()));
            }
        }
        let mut refinement_names = BTreeSet::new();
        for refinement in &self.refinement_types {
            if !refinement_names.insert(refinement.name.as_str()) {
                errors.push(ValidationError::DuplicateName(refinement.name.clone()));
            }
            if !category_names.contains(refinement.base_category.as_str()) {
                errors.push(ValidationError::UnknownSemanticReference {
                    owner: "refinement.base_category",
                    name: refinement.base_category.clone(),
                });
            }
        }
        if let Some(guards) = &self.guard_configuration {
            for theory in &guards.theories {
                if !self
                    .capabilities
                    .contains(&Capability::GuardTheory(theory.implementation.clone()))
                {
                    errors.push(ValidationError::MissingCapability(Capability::GuardTheory(
                        theory.implementation.clone(),
                    )));
                }
                if let Some(categories) = &theory.handled_categories {
                    for category in categories {
                        if !category_names.contains(category.as_str()) {
                            errors.push(ValidationError::UnknownSemanticReference {
                                owner: "guard.theory.category",
                                name: category.clone(),
                            });
                        }
                    }
                }
            }
            if let Some(categories) = &guards.channel_categories {
                for category in categories {
                    if !category_names.contains(category.as_str()) {
                        errors.push(ValidationError::UnknownSemanticReference {
                            owner: "guard.channel.category",
                            name: category.clone(),
                        });
                    }
                }
            }
            for join in &guards.join_patterns {
                if !production_labels.contains(join.label.as_str()) {
                    errors.push(ValidationError::UnknownSemanticReference {
                        owner: "guard.join.label",
                        name: join.label.clone(),
                    });
                }
                for category in &join.channel_categories {
                    if !category_names.contains(category.as_str()) {
                        errors.push(ValidationError::UnknownSemanticReference {
                            owner: "guard.join.category",
                            name: category.clone(),
                        });
                    }
                }
            }
            for (name, value) in &guards.selectivity_overrides {
                if name.is_empty() || !value.is_finite() || !(0.0..=1.0).contains(value) {
                    errors.push(ValidationError::InvalidSelectivity(name.clone()));
                }
            }
        }
        if self.categories.len() > self.limits.max_categories as usize {
            errors.push(ValidationError::LimitExceeded("categories"));
        }
        if self.tokens.len() > self.limits.max_tokens as usize {
            errors.push(ValidationError::LimitExceeded("tokens"));
        }
        if self.productions.len() > self.limits.max_productions as usize {
            errors.push(ValidationError::LimitExceeded("productions"));
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

fn validate_parser_configuration(
    configuration: &ParserConfiguration,
    errors: &mut Vec<ValidationError>,
) {
    if let BeamWidth::Explicit(value) = configuration.beam_width {
        if !value.is_finite() || value < 0.0 {
            errors.push(ValidationError::InvalidParserNumber("beam_width"));
        }
    }
    let recovery = &configuration.recovery;
    for (name, value) in [
        ("skip_per_token", recovery.skip_per_token),
        ("delete_cost", recovery.delete_cost),
        ("substitute_cost", recovery.substitute_cost),
        ("insert_cost", recovery.insert_cost),
        ("swap_cost", recovery.swap_cost),
        ("deep_nesting_skip_mult", recovery.deep_nesting_skip_mult),
        ("shallow_depth_skip_mult", recovery.shallow_depth_skip_mult),
        ("low_bp_skip_mult", recovery.low_bp_skip_mult),
        ("collection_insert_mult", recovery.collection_insert_mult),
        ("group_insert_mult", recovery.group_insert_mult),
        ("bracket_insert_mult", recovery.bracket_insert_mult),
        ("mixfix_substitute_mult", recovery.mixfix_substitute_mult),
        ("simulation_valid_mult", recovery.simulation_valid_mult),
        ("simulation_fail_penalty", recovery.simulation_fail_penalty),
        ("adaptive_weight_threshold", recovery.adaptive_weight_threshold),
        ("deterministic_skip_discount", recovery.deterministic_skip_discount),
        ("ambiguous_insert_discount", recovery.ambiguous_insert_discount),
    ] {
        if !value.is_finite() || value < 0.0 {
            errors.push(ValidationError::InvalidParserNumber(name));
        }
    }
    if recovery
        .beam_width
        .is_some_and(|value| !value.is_finite() || value < 0.0)
    {
        errors.push(ValidationError::InvalidParserNumber("recovery.beam_width"));
    }
}

fn validate_native_evaluation(
    evaluation: &NativeEvaluation,
    capabilities: &BTreeSet<Capability>,
    errors: &mut Vec<ValidationError>,
) {
    match evaluation {
        NativeEvaluation::Operator(name) => {
            const OPERATORS: &[&str] = &[
                "add", "sub", "mul", "div", "mod", "neg", "eq", "ne", "lt", "gt", "le", "ge",
                "and", "or", "xor", "not", "concat", "len",
            ];
            if !OPERATORS.contains(&name.as_str()) {
                errors.push(ValidationError::UnknownNativeOperator(name.clone()));
            }
        },
        NativeEvaluation::Carrier { kind, parameters } => {
            const KINDS: &[&str] = &["int", "rat", "fixed", "float", "bool", "str"];
            const PARAMETERS: &[&str] =
                &["suffix", "require_suffix", "exclude_suffix", "allow_overflow_of"];
            if !KINDS.contains(&kind.as_str()) {
                errors.push(ValidationError::UnknownNativeCarrier(kind.clone()));
            }
            if let Some(key) = parameters
                .keys()
                .find(|key| !PARAMETERS.contains(&key.as_str()))
            {
                errors.push(ValidationError::UnknownNativeCarrierParameter(key.clone()));
            }
        },
        NativeEvaluation::Handler(urn) => {
            if !capabilities.contains(&Capability::NativeEvaluator(urn.clone())) {
                errors.push(ValidationError::MissingCapability(Capability::NativeEvaluator(
                    urn.clone(),
                )));
            }
        },
        NativeEvaluation::Source { semantics, text } => {
            if semantics.is_empty() || semantics.iter().any(String::is_empty) || text.is_empty() {
                errors.push(ValidationError::EmptySemanticName("native.source"));
            }
        },
    }
}

fn validate_dense_ids<T>(
    values: &[T],
    id: impl Fn(&T) -> u32,
    entity: Entity,
    errors: &mut Vec<ValidationError>,
) {
    for (expected, value) in values.iter().enumerate() {
        if id(value) != expected as u32 {
            errors.push(ValidationError::NonDenseId {
                entity,
                expected: expected as u32,
                actual: id(value),
            });
        }
    }
}

fn validate_syntax(
    items: &[SyntaxItem],
    production: ProductionId,
    categories: u32,
    tokens: u32,
    max_depth: u16,
    errors: &mut Vec<ValidationError>,
) {
    let mut pending: Vec<_> = items.iter().rev().map(|item| (item, 1u32)).collect();
    while let Some((item, depth)) = pending.pop() {
        if depth > u32::from(max_depth) {
            errors.push(ValidationError::SyntaxDepthExceeded {
                production: production.0,
                limit: max_depth,
            });
            return;
        }
        match item {
            SyntaxItem::Token(token) | SyntaxItem::CaptureToken { token, .. } => {
                if token.0 >= tokens {
                    errors.push(ValidationError::BadReference {
                        owner: Entity::Production,
                        id: production.0,
                        field: "syntax.token",
                        target: token.0,
                    });
                }
            },
            SyntaxItem::Category { category, .. } | SyntaxItem::Binder { category, .. } => {
                if category.0 >= categories {
                    errors.push(ValidationError::BadReference {
                        owner: Entity::Production,
                        id: production.0,
                        field: "syntax.category",
                        target: category.0,
                    });
                }
            },
            SyntaxItem::Collection {
                element, key, kind, key_value_separator, ..
            } => {
                for category in std::iter::once(element).chain(key.iter()) {
                    if category.0 >= categories {
                        errors.push(ValidationError::BadReference {
                            owner: Entity::Production,
                            id: production.0,
                            field: "syntax.collection.category",
                            target: category.0,
                        });
                    }
                }
                let is_map = matches!(kind, CollectionKind::Map | CollectionKind::PathMap);
                if is_map != key.is_some() || is_map != key_value_separator.is_some() {
                    errors.push(ValidationError::InvalidSyntaxShape {
                        production: production.0,
                        shape: "collection key/value contract",
                    });
                }
            },
            SyntaxItem::Repeat { body, .. }
            | SyntaxItem::Optional(body)
            | SyntaxItem::Sequence(body) => {
                pending.extend(body.iter().rev().map(|nested| (nested, depth + 1)))
            },
            SyntaxItem::Zip { body, .. } => {
                if !body.is_empty() {
                    errors.push(ValidationError::InvalidSyntaxShape {
                        production: production.0,
                        shape: "zip source must not contain a syntax body",
                    });
                }
            },
            SyntaxItem::Separated { source, .. } => pending.push((source, depth + 1)),
            SyntaxItem::Mapped { source, bindings, body } => {
                let source_slots = syntax_slot_names(std::slice::from_ref(source.as_ref()));
                let body_slots = syntax_slot_names(body);
                if source_slots.len() != bindings.len()
                    || body_slots.len() != bindings.len()
                    || body_slots
                        .iter()
                        .zip(bindings)
                        .any(|(slot, binding)| *slot != binding)
                {
                    errors.push(ValidationError::InvalidSyntaxShape {
                        production: production.0,
                        shape: "mapped source/binding/body arity",
                    });
                }
                pending.push((source, depth + 1));
                pending.extend(body.iter().rev().map(|nested| (nested, depth + 1)));
            },
            SyntaxItem::CaptureIdent { .. }
            | SyntaxItem::ForeignLanguage { .. }
            | SyntaxItem::Guard { .. } => {},
        }
    }
}

fn syntax_slot_names(items: &[SyntaxItem]) -> Vec<&str> {
    let mut output = Vec::new();
    let mut pending: Vec<_> = items.iter().rev().collect();
    while let Some(item) = pending.pop() {
        match item {
            SyntaxItem::Category { slot, .. }
            | SyntaxItem::CaptureIdent { slot }
            | SyntaxItem::CaptureToken { slot, .. }
            | SyntaxItem::Binder { slot, .. }
            | SyntaxItem::Collection { slot, .. }
            | SyntaxItem::ForeignLanguage { slot, .. }
            | SyntaxItem::Guard { slot } => output.push(slot.as_str()),
            SyntaxItem::Repeat { body, .. }
            | SyntaxItem::Sequence(body)
            | SyntaxItem::Optional(body) => pending.extend(body.iter().rev()),
            SyntaxItem::Zip { left_slot, right_slot, .. } => {
                output.push(left_slot);
                output.push(right_slot);
            },
            SyntaxItem::Separated { source, .. } | SyntaxItem::Mapped { source, .. } => {
                pending.push(source);
            },
            SyntaxItem::Token(_) => {},
        }
    }
    output
}

fn syntax_slot_count(items: &[SyntaxItem]) -> usize {
    syntax_slot_names(items).len()
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Category {
    pub id: CategoryId,
    pub name: String,
    pub carrier: Carrier,
    pub primary: bool,
    pub admits_variables: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Carrier {
    Dynamic,
    Builtin(BuiltinCarrier),
    Collection(CollectionCarrier),
    Extern { urn: String },
    HostOpaque { stable_name: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollectionCarrier {
    pub kind: CollectionKind,
    pub key: String,
    pub value: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BuiltinCarrier {
    Boolean,
    Integer,
    Rational,
    FixedPoint,
    Float,
    String,
    Bytes,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TokenDefinition {
    pub id: TokenId,
    pub name: String,
    pub pattern: TokenPattern,
    pub category: Option<CategoryId>,
    pub evaluation: Option<NativeEvaluation>,
    pub priority: i16,
    pub mode: ModeId,
    pub channel: String,
    pub transition: ModeTransition,
    pub decoder: TokenDecoder,
    pub reservation: Reservation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TokenPattern {
    Literal(String),
    Regex(String),
    Builtin(BuiltinToken),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BuiltinToken {
    Identifier,
    Integer,
    Float,
    String,
    Boolean,
    EndOfInput,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TokenDecoder {
    Text,
    Integer {
        radix: Option<u8>,
    },
    Boolean {
        true_text: String,
        false_text: String,
    },
    BytesHex,
    Unit,
    /// A stable capability resolved by the embedding runtime, never source code.
    Capability(String),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModeTransition {
    pub push: Option<ModeId>,
    pub pop: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Reservation {
    None,
    Reserved,
    Contextual,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexerMode {
    pub id: ModeId,
    pub name: String,
    pub token_ids: Vec<TokenId>,
    pub raw: bool,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ParserConfiguration {
    pub beam_width: BeamWidth,
    pub log_semiring_model_path: Option<String>,
    pub recovery: RecoveryConfiguration,
    pub reservation: KeywordReservation,
}

impl Default for ParserConfiguration {
    fn default() -> Self {
        Self {
            beam_width: BeamWidth::Disabled,
            log_semiring_model_path: None,
            recovery: RecoveryConfiguration::default(),
            reservation: KeywordReservation::None,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Serialize, Deserialize)]
pub enum BeamWidth {
    #[default]
    Disabled,
    Explicit(f64),
    Auto,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct RecoveryConfiguration {
    pub skip_per_token: f64,
    pub delete_cost: f64,
    pub substitute_cost: f64,
    pub insert_cost: f64,
    pub swap_cost: f64,
    pub max_skip_lookahead: u32,
    pub deep_nesting_threshold: u32,
    pub deep_nesting_skip_mult: f64,
    pub shallow_depth_threshold: u32,
    pub shallow_depth_skip_mult: f64,
    pub low_bp_threshold: u8,
    pub low_bp_skip_mult: f64,
    pub collection_insert_mult: f64,
    pub group_insert_mult: f64,
    pub bracket_insert_mult: f64,
    pub mixfix_substitute_mult: f64,
    pub simulation_valid_mult: f64,
    pub simulation_fail_penalty: f64,
    pub beam_width: Option<f64>,
    pub cascade_window: u32,
    pub vpa_nesting_ceiling: Option<u32>,
    pub adaptive_weight_threshold: f64,
    pub deterministic_skip_discount: f64,
    pub ambiguous_insert_discount: f64,
    pub max_recovery_depth: u8,
}

impl Default for RecoveryConfiguration {
    fn default() -> Self {
        Self {
            skip_per_token: 0.5,
            delete_cost: 1.0,
            substitute_cost: 1.5,
            insert_cost: 2.0,
            swap_cost: 1.25,
            max_skip_lookahead: 32,
            deep_nesting_threshold: 1000,
            deep_nesting_skip_mult: 0.5,
            shallow_depth_threshold: 10,
            shallow_depth_skip_mult: 2.0,
            low_bp_threshold: 4,
            low_bp_skip_mult: 0.75,
            collection_insert_mult: 0.5,
            group_insert_mult: 0.5,
            bracket_insert_mult: 0.3,
            mixfix_substitute_mult: 0.75,
            simulation_valid_mult: 0.5,
            simulation_fail_penalty: 0.2,
            beam_width: Some(3.0),
            cascade_window: 3,
            vpa_nesting_ceiling: None,
            adaptive_weight_threshold: 1.0,
            deterministic_skip_discount: 0.75,
            ambiguous_insert_discount: 0.5,
            max_recovery_depth: 3,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum KeywordReservation {
    #[default]
    None,
    Auto {
        contextual: BTreeSet<String>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SyncConstraint {
    Align {
        stream_a: String,
        stream_b: String,
        boundary_pattern: String,
    },
    Track {
        auxiliary: String,
        primary: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TreeInvariant {
    pub name: String,
    pub formula: CanonicalValue,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RefinementPredicateKind {
    Presburger,
    Behavioral,
    Structural,
    Mixed,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefinementType {
    pub name: String,
    pub base_category: String,
    pub variable_name: String,
    pub predicate_kind: RefinementPredicateKind,
    pub predicate: CanonicalValue,
}

#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct GuardConfiguration {
    pub theories: Vec<GuardTheory>,
    pub channel_categories: Option<Vec<String>>,
    pub join_patterns: Vec<JoinPattern>,
    pub selectivity_overrides: BTreeMap<String, f64>,
    pub cost_overrides: BTreeMap<String, u32>,
    pub has_explicit_connectives: bool,
    pub has_explicit_predicates: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GuardTheory {
    pub name: String,
    pub implementation: String,
    pub handled_categories: Option<Vec<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JoinPattern {
    pub label: String,
    pub channel_categories: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Production {
    pub id: ProductionId,
    pub constructor: ConstructorId,
    pub label: String,
    pub result: CategoryId,
    pub syntax: Vec<SyntaxItem>,
    pub precedence: Precedence,
    pub classification: ProductionClass,
    pub reduction: u32,
    pub provenance: Option<SourceProvenance>,
}

impl Production {
    /// A homogeneous binary application whose operator is juxtaposition.
    /// This is a binding shape, not a generated lexer/Pratt dispatch flag:
    /// no terminal trigger is invented and heterogeneous or delimited forms
    /// keep their separately declared binding contracts.
    pub fn is_binary_juxtaposition(&self) -> bool {
        matches!(
            self.syntax.as_slice(),
            [SyntaxItem::Category { category: left, .. },
             SyntaxItem::Category { category: right, .. }]
                if *left == self.result && *right == self.result
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SyntaxItem {
    Token(TokenId),
    Category {
        category: CategoryId,
        slot: String,
    },
    CaptureIdent {
        slot: String,
    },
    CaptureToken {
        token: TokenId,
        slot: String,
    },
    Binder {
        slot: String,
        category: CategoryId,
        multiple: bool,
    },
    Collection {
        slot: String,
        key: Option<CategoryId>,
        element: CategoryId,
        separator: String,
        kind: CollectionKind,
        key_value_separator: Option<String>,
    },
    Repeat {
        body: Vec<SyntaxItem>,
        separator: String,
        kind: CollectionKind,
    },
    Sequence(Vec<SyntaxItem>),
    Zip {
        left_slot: String,
        right_slot: String,
        left_kind: CollectionKind,
        right_kind: CollectionKind,
        body: Vec<SyntaxItem>,
    },
    Optional(Vec<SyntaxItem>),
    Separated {
        source: Box<SyntaxItem>,
        separator: String,
    },
    Mapped {
        source: Box<SyntaxItem>,
        bindings: Vec<String>,
        body: Vec<SyntaxItem>,
    },
    ForeignLanguage {
        slot: String,
        open: String,
        close: String,
    },
    Guard {
        slot: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum CollectionKind {
    Bag,
    Set,
    List,
    Map,
    PathMap,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Precedence {
    pub binding_power: Option<u16>,
    pub associativity: Associativity,
    pub shares_previous_level: bool,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum Associativity {
    #[default]
    Left,
    Right,
    NonAssociative,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProductionClass {
    pub infix: bool,
    pub postfix: bool,
    pub prefix: bool,
    pub variable: bool,
    pub literal: bool,
    pub binder: bool,
    pub collection: bool,
    pub cross_category: bool,
    pub cast: bool,
    pub generated: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Provenance {
    pub source_uri: Option<String>,
    pub source_hash: Option<[u8; 32]>,
    pub frontend: String,
    pub attributes: BTreeMap<String, String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceProvenance {
    pub uri: Option<String>,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Capability {
    TokenDecoder(String),
    GuardTheory(String),
    SemanticPredicate(String),
    NativeEvaluator(String),
    ExternCarrier(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrammarLimits {
    pub max_categories: u32,
    pub max_tokens: u32,
    pub max_productions: u32,
    pub max_syntax_depth: u16,
    pub max_input_bytes: u32,
    pub max_parse_items: u32,
    pub max_forest_nodes: u32,
    pub max_semantic_results: u32,
}

impl Default for GrammarLimits {
    fn default() -> Self {
        Self {
            max_categories: 65_536,
            max_tokens: 65_536,
            max_productions: 1_000_000,
            max_syntax_depth: 256,
            max_input_bytes: 16 * 1024 * 1024,
            max_parse_items: 10_000_000,
            max_forest_nodes: 10_000_000,
            max_semantic_results: 1_000_000,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Entity {
    Category,
    Token,
    Mode,
    Production,
    Constructor,
    Reduction,
    SemanticDependency,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValidationError {
    UnsupportedAbi(u16),
    NonDenseId {
        entity: Entity,
        expected: u32,
        actual: u32,
    },
    DuplicateName(String),
    DuplicateReference {
        owner: Entity,
        id: u32,
        field: &'static str,
        target: u32,
    },
    MismatchedReference {
        owner: Entity,
        id: u32,
        field: &'static str,
        target: u32,
    },
    BadReference {
        owner: Entity,
        id: u32,
        field: &'static str,
        target: u32,
    },
    TokenModeMembership {
        token: u32,
        occurrences: usize,
    },
    BadReductionInput {
        reduction: u32,
        input: u16,
        arity: u16,
    },
    ReductionSyntaxArity {
        production: u32,
        reduction: u32,
        syntax: usize,
        reduction_arity: u16,
    },
    InvalidSyntaxShape {
        production: u32,
        shape: &'static str,
    },
    SyntaxDepthExceeded {
        production: u32,
        limit: u16,
    },
    MissingCapability(Capability),
    EmptySemanticName(&'static str),
    UnknownSemanticReference {
        owner: &'static str,
        name: String,
    },
    InvalidSelectivity(String),
    InvalidParserNumber(&'static str),
    IncompleteNativeEvaluation(u32),
    UnknownNativeOperator(String),
    UnknownNativeCarrier(String),
    UnknownNativeCarrierParameter(String),
    LimitExceeded(&'static str),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn one_category_core() -> GrammarCoreV1 {
        let mut core = GrammarCoreV1::new("Test");
        core.categories.push(Category {
            id: CategoryId(0),
            name: "Term".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        core
    }

    #[test]
    fn diagnostic_provenance_does_not_change_semantic_identity() {
        let mut left = one_category_core();
        left.name = "Same".into();
        let mut right = left.clone();
        left.provenance.frontend = "module-surface".into();
        left.provenance.source_uri = Some("rho:example".into());
        right.provenance.frontend = "language/2".into();
        right.provenance.source_uri = Some("file:local.module".into());
        assert_eq!(
            left.fingerprint().expect("fingerprint"),
            right.fingerprint().expect("fingerprint")
        );
    }

    #[test]
    fn stale_grammar_abi_is_rejected_before_fingerprinted_artifacts_are_admitted() {
        let mut core = one_category_core();
        core.abi = GRAMMAR_CORE_ABI_V1;
        assert!(matches!(
            core.validate(),
            Err(errors) if errors.contains(&ValidationError::UnsupportedAbi(GRAMMAR_CORE_ABI_V1))
        ));
    }

    #[test]
    fn capability_decoders_must_be_declared() {
        let mut core = one_category_core();
        core.tokens.push(TokenDefinition {
            id: TokenId(0),
            name: "Number".into(),
            pattern: TokenPattern::Builtin(BuiltinToken::Float),
            category: None,
            evaluation: None,
            priority: 0,
            mode: ModeId(0),
            channel: "main".into(),
            transition: ModeTransition::default(),
            decoder: TokenDecoder::Capability("number/decode".into()),
            reservation: Reservation::None,
        });
        core.modes[0].token_ids.push(TokenId(0));

        let errors = core
            .validate()
            .expect_err("undeclared capability must fail");
        assert!(errors.iter().any(|error| matches!(
            error,
            ValidationError::MissingCapability(Capability::TokenDecoder(name))
                if name == "number/decode"
        )));
    }

    #[test]
    fn reduction_inputs_and_nested_syntax_are_bounded() {
        let mut core = one_category_core();
        core.limits.max_syntax_depth = 1;
        core.reductions.push(ReductionPlan {
            output_category: CategoryId(0),
            constructor: ConstructorId(0),
            input_arity: 1,
            fields: vec![crate::FieldSource::Input(1)],
            evaluation: None,
            evaluation_mode: None,
            tier: None,
        });
        core.productions.push(Production {
            id: ProductionId(0),
            constructor: ConstructorId(0),
            label: "Nested".into(),
            result: CategoryId(0),
            syntax: vec![SyntaxItem::Optional(vec![SyntaxItem::CaptureIdent { slot: "x".into() }])],
            precedence: Precedence::default(),
            classification: ProductionClass::default(),
            reduction: 0,
            provenance: None,
        });

        let errors = core
            .validate()
            .expect_err("invalid reduction and depth must fail");
        assert!(errors.iter().any(|error| matches!(
            error,
            ValidationError::BadReductionInput { input: 1, arity: 1, .. }
        )));
        assert!(errors
            .iter()
            .any(|error| matches!(error, ValidationError::SyntaxDepthExceeded { limit: 1, .. })));
    }
}
