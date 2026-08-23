use crate::{ReductionPlan, WeightProfile};
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

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct GrammarCoreV1 {
    pub abi: u16,
    pub name: String,
    pub categories: Vec<Category>,
    pub tokens: Vec<TokenDefinition>,
    pub modes: Vec<LexerMode>,
    pub productions: Vec<Production>,
    pub reductions: Vec<ReductionPlan>,
    pub semantic_dependencies: Vec<Vec<ConstructorId>>,
    pub capabilities: BTreeSet<Capability>,
    pub provenance: Provenance,
    pub limits: GrammarLimits,
    pub weight_profile: WeightProfile,
}

impl GrammarCoreV1 {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            abi: GRAMMAR_CORE_ABI_V1,
            name: name.into(),
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
        semantic.provenance = Provenance::default();
        for production in &mut semantic.productions {
            production.provenance = None;
        }
        let bytes = postcard::to_allocvec(&semantic)?;
        Ok(*blake3::hash(&bytes).as_bytes())
    }

    pub fn validate(&self) -> Result<(), Vec<ValidationError>> {
        let mut errors = Vec::new();
        if self.abi != GRAMMAR_CORE_ABI_V1 {
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
            SyntaxItem::Category { category, .. }
            | SyntaxItem::Binder { category, .. }
            | SyntaxItem::Collection { element: category, .. } => {
                if category.0 >= categories {
                    errors.push(ValidationError::BadReference {
                        owner: Entity::Production,
                        id: production.0,
                        field: "syntax.category",
                        target: category.0,
                    });
                }
            },
            SyntaxItem::Repeat { body, .. }
            | SyntaxItem::Optional(body)
            | SyntaxItem::Zip { body, .. }
            | SyntaxItem::Sequence(body) => {
                pending.extend(body.iter().rev().map(|nested| (nested, depth + 1)))
            },
            SyntaxItem::CaptureIdent { .. } | SyntaxItem::Guard { .. } => {},
        }
    }
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
    HostOpaque { stable_name: String },
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
        body: Vec<SyntaxItem>,
    },
    Optional(Vec<SyntaxItem>),
    Guard {
        slot: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
    SyntaxDepthExceeded {
        production: u32,
        limit: u16,
    },
    MissingCapability(Capability),
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
    fn capability_decoders_must_be_declared() {
        let mut core = one_category_core();
        core.tokens.push(TokenDefinition {
            id: TokenId(0),
            name: "Number".into(),
            pattern: TokenPattern::Builtin(BuiltinToken::Float),
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
