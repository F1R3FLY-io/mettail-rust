//! Complete source-neutral language artifacts.
//!
//! [`GrammarCoreV1`] is deliberately only the recognition/construction
//! projection. [`TheoryCoreV1`] carries dynamics, OSLF judgments, effects,
//! interaction/continuation witnesses, `Cost(G)`, and host resource projection.
//! Keeping the two projections separate lets a parser image remain reusable
//! when only semantic theory changes, while [`LanguageCoreV1::fingerprint`]
//! binds both projections for authority, FLTs, theorem channels, and replay.

use crate::{
    BuiltinCarrier, Carrier, GrammarCoreV1, JudgmentAtomV1, JudgmentRuleV1, LanguageRights,
    TheoryEquationV1, TheoryLiteralCarrierV1, TheoryLiteralV1, TheoryPremiseFormV1,
    TheoryRewriteV1, TheoryRuleArenaV1, TheorySortKindV1, TheoryTermFormV1, TheoryTermId,
    TheoryTermNodeV1, TheoryVariableId, TheoryVariableRoleV1, TheoryVariableV1, ValidationError,
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

pub const LANGUAGE_CORE_ABI_V1: u16 = 1;
pub const THEORY_CORE_ABI_V1: u16 = 1;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LanguageCoreV1 {
    pub abi: u16,
    pub grammar: GrammarCoreV1,
    pub theory: TheoryCoreV1,
}

impl LanguageCoreV1 {
    pub fn structural(grammar: GrammarCoreV1) -> Self {
        Self {
            abi: LANGUAGE_CORE_ABI_V1,
            theory: TheoryCoreV1::structural(),
            grammar,
        }
    }

    pub fn grammar_fingerprint(&self) -> Result<[u8; 32], postcard::Error> {
        self.grammar.fingerprint()
    }

    pub fn theory_fingerprint(&self) -> Result<[u8; 32], postcard::Error> {
        self.theory.fingerprint()
    }

    pub fn fingerprint(&self) -> Result<[u8; 32], postcard::Error> {
        let grammar = self.grammar_fingerprint()?;
        let theory = self.theory_fingerprint()?;
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"mettail-language-core/1\0");
        hasher.update(&self.abi.to_be_bytes());
        hasher.update(&grammar);
        hasher.update(&theory);
        Ok(*hasher.finalize().as_bytes())
    }

    pub fn validate(&self) -> Result<(), Vec<LanguageCoreValidationError>> {
        let mut errors = Vec::new();
        if self.abi != LANGUAGE_CORE_ABI_V1 {
            errors.push(LanguageCoreValidationError::UnsupportedLanguageAbi(self.abi));
        }
        if let Err(grammar) = self.grammar.validate() {
            errors.push(LanguageCoreValidationError::Grammar(grammar));
        }
        errors.extend(
            self.theory
                .validation_errors(&self.grammar)
                .into_iter()
                .map(LanguageCoreValidationError::Theory),
        );
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryProfileV1 {
    StructuralOnly,
    Oslf,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryCoreV1 {
    pub abi: u16,
    pub profile: TheoryProfileV1,
    pub sorts: Vec<TheorySortV1>,
    pub constructors: Vec<TheoryConstructorV1>,
    pub binders: Vec<TheoryBinderV1>,
    pub equations: Vec<TheoryEquationV1>,
    pub rewrites: Vec<TheoryRewriteV1>,
    pub actions: Vec<SemanticActionV1>,
    pub judgments: Vec<JudgmentDeclV1>,
    pub observations: Vec<ObservationDeclV1>,
    pub morphisms: Vec<TheoryMorphismV1>,
    pub effects: Vec<EffectDeclV1>,
    pub interactive: Option<InteractiveDeclV1>,
    pub continued: Option<ContinuedDeclV1>,
    pub cost: Option<CostDeclV1>,
    pub resource_projection: Option<ResourceProjectionV1>,
    pub checker_requirements: Vec<CheckerRequirementV1>,
    pub limits: TheoryLimitsV1,
}

impl TheoryCoreV1 {
    pub fn structural() -> Self {
        Self {
            abi: THEORY_CORE_ABI_V1,
            profile: TheoryProfileV1::StructuralOnly,
            sorts: Vec::new(),
            constructors: Vec::new(),
            binders: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            actions: Vec::new(),
            judgments: Vec::new(),
            observations: Vec::new(),
            morphisms: Vec::new(),
            effects: Vec::new(),
            interactive: None,
            continued: None,
            cost: None,
            resource_projection: None,
            checker_requirements: Vec::new(),
            limits: TheoryLimitsV1::default(),
        }
    }

    pub fn fingerprint(&self) -> Result<[u8; 32], postcard::Error> {
        let bytes = postcard::to_allocvec(self)?;
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"mettail-theory-core/1\0");
        hasher.update(&bytes);
        Ok(*hasher.finalize().as_bytes())
    }

    fn validation_errors(&self, grammar: &GrammarCoreV1) -> Vec<TheoryValidationError> {
        let mut errors = Vec::new();
        if self.abi != THEORY_CORE_ABI_V1 {
            errors.push(TheoryValidationError::UnsupportedTheoryAbi(self.abi));
        }
        if self.limits.has_zero_bound() {
            errors.push(TheoryValidationError::ZeroLimit);
        }
        if self.profile == TheoryProfileV1::StructuralOnly && self.has_semantic_structure() {
            errors.push(TheoryValidationError::StructuralProfileContainsOslfData);
        }
        if self.continued.is_some() && self.interactive.is_none() {
            errors.push(TheoryValidationError::ContinuedRequiresInteractive);
        }
        if self.cost.is_some() && self.continued.is_none() {
            errors.push(TheoryValidationError::CostRequiresContinued);
        }

        unique_names(self.sorts.iter().map(|value| value.name.as_str()), "sort", &mut errors);
        unique_names(
            self.constructors.iter().map(|value| value.name.as_str()),
            "constructor",
            &mut errors,
        );
        unique_names(self.binders.iter().map(|value| value.name.as_str()), "binder", &mut errors);
        unique_names(self.actions.iter().map(|value| value.id.as_str()), "action", &mut errors);
        unique_names(
            self.judgments.iter().map(|value| value.name.as_str()),
            "judgment",
            &mut errors,
        );
        unique_names(
            self.observations.iter().map(|value| value.name.as_str()),
            "observation",
            &mut errors,
        );
        unique_names(
            self.morphisms.iter().map(|value| value.name.as_str()),
            "morphism",
            &mut errors,
        );
        unique_names(self.effects.iter().map(|value| value.name.as_str()), "effect", &mut errors);
        unique_names(
            self.equations.iter().map(|value| value.name.as_str()),
            "equation",
            &mut errors,
        );
        unique_names(self.rewrites.iter().map(|value| value.name.as_str()), "rewrite", &mut errors);

        let mut sorts: BTreeSet<&str> = grammar
            .categories
            .iter()
            .map(|category| category.name.as_str())
            .collect();
        sorts.extend(self.sorts.iter().map(|sort| sort.name.as_str()));
        let sort_declarations: BTreeMap<_, _> = self
            .sorts
            .iter()
            .map(|sort| (sort.name.as_str(), sort))
            .collect();
        let effects: BTreeSet<&str> = self
            .effects
            .iter()
            .map(|effect| effect.name.as_str())
            .collect();
        let actions: BTreeSet<&str> = self
            .actions
            .iter()
            .map(|action| action.id.as_str())
            .collect();
        let judgments: BTreeMap<&str, &JudgmentDeclV1> = self
            .judgments
            .iter()
            .map(|judgment| (judgment.name.as_str(), judgment))
            .collect();

        validate_signature(self, grammar, &sorts, &mut errors);

        let constructors: std::collections::BTreeMap<_, _> = self
            .constructors
            .iter()
            .map(|value| (value.name.as_str(), value))
            .collect();
        let validation = TheoryValidationContext {
            sorts: &sort_declarations,
            constructors: &constructors,
            judgments: &judgments,
            limits: self.limits,
        };
        for equation in &self.equations {
            validate_rule_arena(
                &equation.name,
                &equation.arena,
                equation.left,
                equation.right,
                false,
                &validation,
                &mut errors,
            );
        }
        for rewrite in &self.rewrites {
            validate_rule_arena(
                &rewrite.name,
                &rewrite.arena,
                rewrite.left,
                rewrite.right,
                true,
                &validation,
                &mut errors,
            );
        }
        for action in &self.actions {
            require_sorts(action.domain.iter().map(String::as_str), &sorts, &mut errors);
            require_sort(&action.codomain, &sorts, &mut errors);
            require_sort(&action.grade, &sorts, &mut errors);
            if let Some(cost) = &self.cost {
                if action.grade != cost.signature_sort {
                    errors.push(TheoryValidationError::SortMismatch {
                        owner: format!("action `{}` resource grade", action.id),
                        expected: cost.signature_sort.clone(),
                        actual: action.grade.clone(),
                    });
                }
            }
            if !effects.contains(action.effect.as_str()) {
                errors.push(TheoryValidationError::UnknownReference {
                    kind: "effect",
                    name: action.effect.clone(),
                });
            }
            if let Some(effect) = self
                .effects
                .iter()
                .find(|effect| effect.name == action.effect)
            {
                if effect.class != action.effect_class {
                    errors.push(TheoryValidationError::UnknownReference {
                        kind: "effect class",
                        name: format!("{}::{:?}", action.effect, action.effect_class),
                    });
                }
            }
            if !action
                .required_rights
                .is_subset_of(&grammar.requested_rights)
            {
                errors.push(TheoryValidationError::UnknownReference {
                    kind: "requested right",
                    name: action.id.clone(),
                });
            }
            match &action.transition {
                TheoryRuleReferenceV1::Rewrite(name)
                    if !self.rewrites.iter().any(|rule| rule.name == *name) =>
                {
                    errors.push(TheoryValidationError::UnknownReference {
                        kind: "rewrite",
                        name: name.clone(),
                    });
                },
                TheoryRuleReferenceV1::Equation(name)
                    if !self.equations.iter().any(|rule| rule.name == *name) =>
                {
                    errors.push(TheoryValidationError::UnknownReference {
                        kind: "equation",
                        name: name.clone(),
                    });
                },
                TheoryRuleReferenceV1::Handler(name) if name.is_empty() => {
                    errors.push(TheoryValidationError::UnknownReference {
                        kind: "handler",
                        name: name.clone(),
                    });
                },
                TheoryRuleReferenceV1::Rewrite(_)
                | TheoryRuleReferenceV1::Equation(_)
                | TheoryRuleReferenceV1::Handler(_) => {},
            }
            validate_rule_backed_action_signature(action, self, &mut errors);
        }
        for judgment in &self.judgments {
            require_sorts(judgment.arguments.iter().map(String::as_str), &sorts, &mut errors);
            for rule in &judgment.rules {
                validate_judgment_rule(
                    judgment,
                    rule,
                    &sort_declarations,
                    &constructors,
                    &judgments,
                    self.limits,
                    &mut errors,
                );
            }
        }
        for observation in &self.observations {
            if !actions.contains(observation.action.as_str()) {
                errors.push(TheoryValidationError::UnknownReference {
                    kind: "action",
                    name: observation.action.clone(),
                });
            }
            require_sort(&observation.result, &sorts, &mut errors);
        }
        if let Some(interactive) = &self.interactive {
            require_sorts(
                [
                    interactive.channel_sort.as_str(),
                    interactive.datum_sort.as_str(),
                    interactive.continuation_sort.as_str(),
                ],
                &sorts,
                &mut errors,
            );
        }
        if let Some(cost) = &self.cost {
            require_sorts(
                [
                    cost.signature_sort.as_str(),
                    cost.stack_sort.as_str(),
                    cost.wrapped_sort.as_str(),
                    cost.located_sort.as_str(),
                ],
                &sorts,
                &mut errors,
            );
        }
        if let Some(projection) = &self.resource_projection {
            require_sorts(
                [projection.grade_sort.as_str(), projection.demand_sort.as_str()],
                &sorts,
                &mut errors,
            );
        }
        unique_names(
            self.checker_requirements
                .iter()
                .map(|checker| checker.abi.as_str()),
            "checker ABI",
            &mut errors,
        );
        errors
    }

    fn has_semantic_structure(&self) -> bool {
        !self.sorts.is_empty()
            || !self.constructors.is_empty()
            || !self.binders.is_empty()
            || !self.equations.is_empty()
            || !self.rewrites.is_empty()
            || !self.actions.is_empty()
            || !self.judgments.is_empty()
            || !self.observations.is_empty()
            || !self.morphisms.is_empty()
            || !self.effects.is_empty()
            || self.interactive.is_some()
            || self.continued.is_some()
            || self.cost.is_some()
            || self.resource_projection.is_some()
            || !self.checker_requirements.is_empty()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheorySortV1 {
    pub name: String,
    pub kind: TheorySortKindV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryConstructorV1 {
    pub name: String,
    pub domain: Vec<String>,
    pub codomain: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryBinderV1 {
    pub name: String,
    pub constructor: String,
    pub argument: u16,
    pub bound_sort: String,
    pub body_sort: String,
    pub result_sort: String,
    pub multiple: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticActionV1 {
    pub id: String,
    pub domain: Vec<String>,
    pub codomain: String,
    pub transition: TheoryRuleReferenceV1,
    pub effect: String,
    pub effect_class: SemanticEffectClassV1,
    pub required_rights: LanguageRights,
    pub grade: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SemanticEffectClassV1 {
    Pure,
    Structural,
    Behavioral,
    Resource,
    External,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryRuleReferenceV1 {
    Rewrite(String),
    Equation(String),
    Handler(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum JudgmentDecisionV1 {
    Exact,
    Bounded,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JudgmentDeclV1 {
    pub name: String,
    pub arguments: Vec<String>,
    pub decision: JudgmentDecisionV1,
    pub rules: Vec<JudgmentRuleV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservationDeclV1 {
    pub name: String,
    pub action: String,
    pub result: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryMorphismV1 {
    pub name: String,
    pub source: String,
    pub target: String,
    pub categories: Vec<(String, String)>,
    pub constructors: Vec<(String, String)>,
    pub actions: Vec<(String, String)>,
    pub grades: Vec<(String, String)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EffectDeclV1 {
    pub name: String,
    pub class: SemanticEffectClassV1,
    pub requires: Vec<String>,
    pub emits: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InteractiveDeclV1 {
    pub cut: String,
    pub channel_sort: String,
    pub datum_sort: String,
    pub continuation_sort: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContinuedDeclV1 {
    pub k: String,
    pub kp: String,
    pub ke: String,
    pub k_prime: String,
    pub near: String,
    pub compute: String,
    pub section: String,
    pub wrappability: String,
    pub quote_faithfulness: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CostDeclV1 {
    pub base: String,
    pub signature_sort: String,
    pub stack_sort: String,
    pub wrapped_sort: String,
    pub located_sort: String,
    pub product: String,
    pub unit: String,
    pub rules: Vec<String>,
    pub eta: String,
    pub mu: String,
    pub map: String,
    pub laws: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResourceProjectionV1 {
    pub abi: String,
    pub grade_sort: String,
    pub demand_sort: String,
    pub project: String,
    pub proof: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckerRequirementV1 {
    pub abi: String,
    pub limit_profile: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryLimitsV1 {
    pub max_rule_variables: u32,
    pub max_term_nodes: u32,
    pub max_premise_nodes: u32,
    pub max_proof_nodes: u32,
    pub max_frontier: u32,
    pub max_steps: u32,
    pub max_grade_bits: u32,
    pub max_output_nodes: u32,
    pub max_output_bytes: u32,
}

impl TheoryLimitsV1 {
    fn has_zero_bound(self) -> bool {
        self.max_rule_variables == 0
            || self.max_term_nodes == 0
            || self.max_premise_nodes == 0
            || self.max_proof_nodes == 0
            || self.max_frontier == 0
            || self.max_steps == 0
            || self.max_grade_bits == 0
            || self.max_output_nodes == 0
            || self.max_output_bytes == 0
    }
}

impl Default for TheoryLimitsV1 {
    fn default() -> Self {
        Self {
            max_rule_variables: 65_536,
            max_term_nodes: 1_000_000,
            max_premise_nodes: 1_000_000,
            max_proof_nodes: 1_000_000,
            max_frontier: 100_000,
            max_steps: 10_000_000,
            max_grade_bits: 4096,
            max_output_nodes: 1_000_000,
            max_output_bytes: 16 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LanguageCoreValidationError {
    UnsupportedLanguageAbi(u16),
    Grammar(Vec<ValidationError>),
    Theory(TheoryValidationError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoryValidationError {
    UnsupportedTheoryAbi(u16),
    ZeroLimit,
    TermLimitExceeded {
        actual: usize,
        limit: u32,
    },
    StructuralProfileContainsOslfData,
    ContinuedRequiresInteractive,
    CostRequiresContinued,
    DuplicateName {
        kind: &'static str,
        name: String,
    },
    UnknownReference {
        kind: &'static str,
        name: String,
    },
    UnknownTerm(u32),
    UnknownVariable(u32),
    UnknownPremise(u32),
    UnreachablePremise(u32),
    SharedPremise(u32),
    NonTopologicalTermReference {
        owner: u32,
        target: u32,
    },
    NonTopologicalPremiseReference {
        owner: u32,
        target: u32,
    },
    TransitionInEquation(String),
    LimitExceeded {
        kind: &'static str,
        actual: usize,
        limit: u32,
    },
    NonDenseId {
        kind: &'static str,
        expected: u32,
        actual: u32,
    },
    SortMismatch {
        owner: String,
        expected: String,
        actual: String,
    },
    ArityMismatch {
        constructor: String,
        expected: usize,
        actual: usize,
    },
    BindingArityMismatch {
        owner: String,
        expected: usize,
        actual: usize,
    },
    UnboundVariable {
        rule: String,
        variable: String,
    },
    InvalidVariableRole {
        rule: String,
        variable: String,
        expected: &'static str,
    },
    PremiseDependency {
        rule: String,
        variable: String,
    },
    NonLinearVariable {
        rule: String,
        variable: String,
    },
    RootSortMismatch {
        rule: String,
        left: String,
        right: String,
    },
    JudgmentOwnerMismatch {
        rule: String,
        expected: String,
        actual: String,
    },
    RuleBackedActionArity {
        action: String,
        actual: usize,
    },
    RuleBackedActionSignature {
        action: String,
        rule: String,
        source: String,
        target: String,
        domain: Vec<String>,
        codomain: String,
    },
}

/// Version-1 `RuleRef` actions label a transition of one canonical term.  A
/// handler ABI may define a richer invocation convention, but a bare rewrite
/// reference contains no mapping from multiple operands into its one redex.
fn validate_rule_backed_action_signature(
    action: &SemanticActionV1,
    theory: &TheoryCoreV1,
    errors: &mut Vec<TheoryValidationError>,
) {
    let mut rules = Vec::new();
    match &action.transition {
        TheoryRuleReferenceV1::Equation(name) => {
            rules.extend(
                theory
                    .equations
                    .iter()
                    .filter(|rule| rule.name == *name)
                    .map(|rule| (rule.name.as_str(), &rule.arena, rule.left, rule.right)),
            );
        },
        TheoryRuleReferenceV1::Rewrite(name) => {
            rules.extend(
                theory
                    .rewrites
                    .iter()
                    .filter(|rule| rule.name == *name)
                    .map(|rule| (rule.name.as_str(), &rule.arena, rule.left, rule.right)),
            );
        },
        TheoryRuleReferenceV1::Handler(_) => return,
    }
    if rules.is_empty() {
        return;
    }
    if action.domain.len() != 1 {
        errors.push(TheoryValidationError::RuleBackedActionArity {
            action: action.id.clone(),
            actual: action.domain.len(),
        });
        return;
    }
    for (rule, arena, left, right) in rules {
        let Some(source) = arena.terms.get(left.0 as usize) else {
            continue;
        };
        let Some(target) = arena.terms.get(right.0 as usize) else {
            continue;
        };
        if action.domain[0] != source.sort || action.codomain != target.sort {
            errors.push(TheoryValidationError::RuleBackedActionSignature {
                action: action.id.clone(),
                rule: rule.to_string(),
                source: source.sort.clone(),
                target: target.sort.clone(),
                domain: action.domain.clone(),
                codomain: action.codomain.clone(),
            });
        }
    }
}

fn unique_names<'a>(
    names: impl IntoIterator<Item = &'a str>,
    kind: &'static str,
    errors: &mut Vec<TheoryValidationError>,
) {
    let mut seen = BTreeSet::new();
    for name in names {
        if name.is_empty() || !seen.insert(name) {
            errors.push(TheoryValidationError::DuplicateName { kind, name: name.to_string() });
        }
    }
}

fn require_sorts<'a>(
    names: impl IntoIterator<Item = &'a str>,
    sorts: &BTreeSet<&str>,
    errors: &mut Vec<TheoryValidationError>,
) {
    for name in names {
        require_sort(name, sorts, errors);
    }
}

fn require_sort(name: &str, sorts: &BTreeSet<&str>, errors: &mut Vec<TheoryValidationError>) {
    if !sorts.contains(name) {
        errors
            .push(TheoryValidationError::UnknownReference { kind: "sort", name: name.to_string() });
    }
}

fn validate_signature(
    theory: &TheoryCoreV1,
    grammar: &GrammarCoreV1,
    sorts: &BTreeSet<&str>,
    errors: &mut Vec<TheoryValidationError>,
) {
    let grammar_categories: BTreeMap<_, _> = grammar
        .categories
        .iter()
        .map(|category| (category.name.as_str(), category))
        .collect();
    for sort in &theory.sorts {
        match &sort.kind {
            TheorySortKindV1::Syntax { literal } => {
                let Some(category) = grammar_categories.get(sort.name.as_str()) else {
                    errors.push(TheoryValidationError::UnknownReference {
                        kind: "grammar category",
                        name: sort.name.clone(),
                    });
                    continue;
                };
                if literal.as_ref() != literal_carrier(&category.carrier).as_ref() {
                    errors.push(TheoryValidationError::SortMismatch {
                        owner: format!("sort `{}` literal carrier", sort.name),
                        expected: format!("{:?}", literal_carrier(&category.carrier)),
                        actual: format!("{literal:?}"),
                    });
                }
            },
            TheorySortKindV1::Collection { key, element, .. } => {
                if let Some(key) = key {
                    require_sort(key, sorts, errors);
                }
                require_sort(element, sorts, errors);
            },
            TheorySortKindV1::Function { domain, codomain, .. } => {
                require_sort(domain, sorts, errors);
                require_sort(codomain, sorts, errors);
            },
            TheorySortKindV1::Product { factors } => {
                if factors.is_empty() {
                    errors.push(TheoryValidationError::UnknownReference {
                        kind: "product sort",
                        name: sort.name.clone(),
                    });
                }
                require_sorts(factors.iter().map(String::as_str), sorts, errors);
            },
            TheorySortKindV1::Opaque { abi } if abi.is_empty() => {
                errors.push(TheoryValidationError::UnknownReference {
                    kind: "opaque sort ABI",
                    name: sort.name.clone(),
                });
            },
            TheorySortKindV1::Opaque { .. } => {},
        }
    }
    if theory.profile == TheoryProfileV1::Oslf {
        for category in &grammar.categories {
            if !theory.sorts.iter().any(|sort| {
                sort.name == category.name && matches!(sort.kind, TheorySortKindV1::Syntax { .. })
            }) {
                errors.push(TheoryValidationError::UnknownReference {
                    kind: "theory sort for grammar category",
                    name: category.name.clone(),
                });
            }
        }
    }
    let grammar_constructors: BTreeMap<_, _> = grammar
        .productions
        .iter()
        .map(|production| (production.label.as_str(), production))
        .collect();
    for constructor in &theory.constructors {
        require_sorts(constructor.domain.iter().map(String::as_str), sorts, errors);
        require_sort(&constructor.codomain, sorts, errors);
        let Some(production) = grammar_constructors.get(constructor.name.as_str()) else {
            errors.push(TheoryValidationError::UnknownReference {
                kind: "grammar constructor",
                name: constructor.name.clone(),
            });
            continue;
        };
        if grammar
            .categories
            .get(production.result.0 as usize)
            .map(|category| category.name.as_str())
            != Some(constructor.codomain.as_str())
        {
            errors.push(TheoryValidationError::SortMismatch {
                owner: format!("constructor `{}`", constructor.name),
                expected: grammar
                    .categories
                    .get(production.result.0 as usize)
                    .map(|category| category.name.clone())
                    .unwrap_or_default(),
                actual: constructor.codomain.clone(),
            });
        }
    }
    if theory.profile == TheoryProfileV1::Oslf {
        for production in &grammar.productions {
            if !theory
                .constructors
                .iter()
                .any(|constructor| constructor.name == production.label)
            {
                errors.push(TheoryValidationError::UnknownReference {
                    kind: "theory constructor for grammar production",
                    name: production.label.clone(),
                });
            }
        }
    }
    let constructors: BTreeMap<_, _> = theory
        .constructors
        .iter()
        .map(|constructor| (constructor.name.as_str(), constructor))
        .collect();
    for binder in &theory.binders {
        let Some(constructor) = constructors.get(binder.constructor.as_str()) else {
            errors.push(TheoryValidationError::UnknownReference {
                kind: "binder constructor",
                name: binder.constructor.clone(),
            });
            continue;
        };
        let Some(argument) = constructor.domain.get(binder.argument as usize) else {
            errors.push(TheoryValidationError::ArityMismatch {
                constructor: binder.constructor.clone(),
                expected: constructor.domain.len(),
                actual: binder.argument as usize + 1,
            });
            continue;
        };
        for sort in [&binder.bound_sort, &binder.body_sort, &binder.result_sort] {
            require_sort(sort, sorts, errors);
        }
        if argument != &binder.result_sort {
            errors.push(TheoryValidationError::SortMismatch {
                owner: format!("binder `{}`", binder.name),
                expected: argument.clone(),
                actual: binder.result_sort.clone(),
            });
        }
        let matching_function = theory.sorts.iter().any(|sort| {
            sort.name == binder.result_sort
                && matches!(
                    &sort.kind,
                    TheorySortKindV1::Function { domain, codomain, multiple }
                        if domain == &binder.bound_sort
                            && codomain == &binder.body_sort
                            && multiple == &binder.multiple
                )
        });
        if !matching_function {
            errors.push(TheoryValidationError::UnknownReference {
                kind: "binder function sort",
                name: binder.result_sort.clone(),
            });
        }
    }
}

fn literal_carrier(carrier: &Carrier) -> Option<TheoryLiteralCarrierV1> {
    Some(match carrier {
        Carrier::Dynamic | Carrier::Collection(_) => return None,
        Carrier::Builtin(BuiltinCarrier::Boolean) => TheoryLiteralCarrierV1::Boolean,
        Carrier::Builtin(BuiltinCarrier::Integer) => TheoryLiteralCarrierV1::Integer,
        Carrier::Builtin(BuiltinCarrier::Rational) => TheoryLiteralCarrierV1::Rational,
        Carrier::Builtin(BuiltinCarrier::FixedPoint) => TheoryLiteralCarrierV1::FixedPoint,
        Carrier::Builtin(BuiltinCarrier::Float) => TheoryLiteralCarrierV1::Float,
        Carrier::Builtin(BuiltinCarrier::String) => TheoryLiteralCarrierV1::String,
        Carrier::Builtin(BuiltinCarrier::Bytes) => TheoryLiteralCarrierV1::Bytes,
        Carrier::Extern { urn } => TheoryLiteralCarrierV1::External(urn.clone()),
        Carrier::HostOpaque { stable_name } => {
            TheoryLiteralCarrierV1::HostOpaque(stable_name.clone())
        },
    })
}

struct TheoryValidationContext<'a> {
    sorts: &'a BTreeMap<&'a str, &'a TheorySortV1>,
    constructors: &'a BTreeMap<&'a str, &'a TheoryConstructorV1>,
    judgments: &'a BTreeMap<&'a str, &'a JudgmentDeclV1>,
    limits: TheoryLimitsV1,
}

struct PremiseValidationContext<'a> {
    rule: &'a str,
    allow_transition: bool,
    arena: &'a TheoryRuleArenaV1,
    sorts: &'a BTreeMap<&'a str, &'a TheorySortV1>,
    judgments: &'a BTreeMap<&'a str, &'a JudgmentDeclV1>,
}

fn validate_rule_arena(
    rule: &str,
    arena: &TheoryRuleArenaV1,
    left: TheoryTermId,
    right: TheoryTermId,
    allow_transition: bool,
    validation: &TheoryValidationContext<'_>,
    errors: &mut Vec<TheoryValidationError>,
) {
    validate_variables(rule, &arena.variables, validation.sorts, validation.limits, errors);
    validate_term_arena(
        rule,
        &arena.variables,
        &arena.terms,
        validation.sorts,
        validation.constructors,
        validation.limits,
        errors,
    );
    validate_limit(
        "premise nodes",
        arena.premises.len(),
        validation.limits.max_premise_nodes,
        errors,
    );
    let Some(left_node) = term_node(rule, &arena.terms, left, errors) else {
        return;
    };
    let Some(right_node) = term_node(rule, &arena.terms, right, errors) else {
        return;
    };
    if left_node.sort != right_node.sort {
        errors.push(TheoryValidationError::RootSortMismatch {
            rule: rule.to_string(),
            left: left_node.sort.clone(),
            right: right_node.sort.clone(),
        });
    }
    let left_occurrences = variable_occurrences(left, &arena.terms);
    let right_occurrences = variable_occurrences(right, &arena.terms);
    let mut available: BTreeSet<_> = left_occurrences.keys().copied().collect();
    for (variable, count) in &left_occurrences {
        let Some(declaration) = arena.variables.get(variable.0 as usize) else {
            continue;
        };
        match declaration.role {
            TheoryVariableRoleV1::Input => {},
            TheoryVariableRoleV1::Binder | TheoryVariableRoleV1::Remainder if *count == 1 => {},
            TheoryVariableRoleV1::Binder | TheoryVariableRoleV1::Remainder => {
                errors.push(TheoryValidationError::NonLinearVariable {
                    rule: rule.to_string(),
                    variable: declaration.name.clone(),
                });
            },
            TheoryVariableRoleV1::Derived | TheoryVariableRoleV1::Quantified => {
                errors.push(TheoryValidationError::InvalidVariableRole {
                    rule: rule.to_string(),
                    variable: declaration.name.clone(),
                    expected: "an input, binder, or remainder variable on the left side",
                });
            },
        }
    }
    let mut previous_root = None;
    let mut premise_uses = vec![0u8; arena.premises.len()];
    let premise_validation = PremiseValidationContext {
        rule,
        allow_transition,
        arena,
        sorts: validation.sorts,
        judgments: validation.judgments,
    };
    for premise_root in &arena.premise_roots {
        if previous_root.is_some_and(|previous| previous >= premise_root.0) {
            errors.push(TheoryValidationError::NonTopologicalPremiseReference {
                owner: premise_root.0,
                target: previous_root.unwrap_or(premise_root.0),
            });
        }
        previous_root = Some(premise_root.0);
        if arena.premises.get(premise_root.0 as usize).is_none() {
            errors.push(TheoryValidationError::UnknownPremise(premise_root.0));
            continue;
        }
        validate_premise_dependencies(
            premise_root.0 as usize,
            &premise_validation,
            &mut available,
            &mut premise_uses,
            errors,
        );
    }
    for (index, uses) in premise_uses.into_iter().enumerate() {
        if uses == 0 {
            errors.push(TheoryValidationError::UnreachablePremise(index as u32));
        }
    }
    for variable in right_occurrences.keys() {
        if !available.contains(variable) {
            let name = arena
                .variables
                .get(variable.0 as usize)
                .map(|value| value.name.clone())
                .unwrap_or_else(|| format!("#{}", variable.0));
            errors.push(TheoryValidationError::UnboundVariable {
                rule: rule.to_string(),
                variable: name,
            });
        }
    }
}

fn validate_variables(
    rule: &str,
    variables: &[TheoryVariableV1],
    sorts: &BTreeMap<&str, &TheorySortV1>,
    limits: TheoryLimitsV1,
    errors: &mut Vec<TheoryValidationError>,
) {
    validate_limit("rule variables", variables.len(), limits.max_rule_variables, errors);
    let mut names = BTreeSet::new();
    for (index, variable) in variables.iter().enumerate() {
        if variable.id.0 != index as u32 {
            errors.push(TheoryValidationError::NonDenseId {
                kind: "theory variable",
                expected: index as u32,
                actual: variable.id.0,
            });
        }
        if variable.name.is_empty() || !names.insert(variable.name.as_str()) {
            errors.push(TheoryValidationError::DuplicateName {
                kind: "rule variable",
                name: format!("{rule}::{}", variable.name),
            });
        }
        require_declared_sort(&variable.sort, sorts, errors);
    }
}

fn validate_term_arena(
    owner: &str,
    variables: &[TheoryVariableV1],
    terms: &[TheoryTermNodeV1],
    sorts: &BTreeMap<&str, &TheorySortV1>,
    constructors: &BTreeMap<&str, &TheoryConstructorV1>,
    limits: TheoryLimitsV1,
    errors: &mut Vec<TheoryValidationError>,
) {
    validate_limit("term nodes", terms.len(), limits.max_term_nodes, errors);
    for (index, node) in terms.iter().enumerate() {
        require_declared_sort(&node.sort, sorts, errors);
        match &node.form {
            TheoryTermFormV1::Variable(variable) => {
                if let Some(declaration) = variables.get(variable.0 as usize) {
                    require_equal_sort(owner, &declaration.sort, &node.sort, errors);
                } else {
                    errors.push(TheoryValidationError::UnknownVariable(variable.0));
                }
            },
            TheoryTermFormV1::Constructor { constructor, arguments } => {
                let Some(declaration) = constructors.get(constructor.as_str()) else {
                    errors.push(TheoryValidationError::UnknownReference {
                        kind: "constructor",
                        name: constructor.clone(),
                    });
                    continue;
                };
                if arguments.len() != declaration.domain.len() {
                    errors.push(TheoryValidationError::ArityMismatch {
                        constructor: constructor.clone(),
                        expected: declaration.domain.len(),
                        actual: arguments.len(),
                    });
                }
                for (argument, expected) in arguments.iter().zip(&declaration.domain) {
                    if let Some(child) = prior_term(owner, terms, index, *argument, errors) {
                        require_equal_sort(owner, expected, &child.sort, errors);
                    }
                }
                require_equal_sort(owner, &declaration.codomain, &node.sort, errors);
            },
            TheoryTermFormV1::Abstraction { binder, body } => {
                let Some(variable) = variables.get(binder.0 as usize) else {
                    errors.push(TheoryValidationError::UnknownVariable(binder.0));
                    continue;
                };
                if variable.role != TheoryVariableRoleV1::Binder {
                    errors.push(TheoryValidationError::InvalidVariableRole {
                        rule: owner.to_string(),
                        variable: variable.name.clone(),
                        expected: "Binder",
                    });
                }
                let Some(body_node) = prior_term(owner, terms, index, *body, errors) else {
                    continue;
                };
                match sorts.get(node.sort.as_str()).map(|sort| &sort.kind) {
                    Some(TheorySortKindV1::Function { domain, codomain, .. }) => {
                        require_equal_sort(owner, domain, &variable.sort, errors);
                        require_equal_sort(owner, codomain, &body_node.sort, errors);
                    },
                    _ => errors.push(TheoryValidationError::UnknownReference {
                        kind: "function sort",
                        name: node.sort.clone(),
                    }),
                }
            },
            TheoryTermFormV1::Substitution { abstraction, argument } => {
                let abstraction = prior_term(owner, terms, index, *abstraction, errors);
                let argument = prior_term(owner, terms, index, *argument, errors);
                if let (Some(abstraction), Some(argument)) = (abstraction, argument) {
                    match sorts.get(abstraction.sort.as_str()).map(|sort| &sort.kind) {
                        Some(TheorySortKindV1::Function { domain, codomain, .. }) => {
                            require_equal_sort(owner, domain, &argument.sort, errors);
                            require_equal_sort(owner, codomain, &node.sort, errors);
                        },
                        _ => errors.push(TheoryValidationError::UnknownReference {
                            kind: "substitution function sort",
                            name: abstraction.sort.clone(),
                        }),
                    }
                }
            },
            TheoryTermFormV1::Collection { elements, remainder } => {
                let (element_sort, collection_sort) =
                    match sorts.get(node.sort.as_str()).map(|sort| &sort.kind) {
                        Some(kind @ TheorySortKindV1::Collection { element, .. }) => {
                            (Some(element.as_str()), Some(kind))
                        },
                        _ => (None, None),
                    };
                if collection_sort.is_none() {
                    errors.push(TheoryValidationError::UnknownReference {
                        kind: "collection sort",
                        name: node.sort.clone(),
                    });
                }
                if let Some(element_sort) = element_sort {
                    for element in elements {
                        if let Some(child) = prior_term(owner, terms, index, *element, errors) {
                            require_equal_sort(owner, element_sort, &child.sort, errors);
                        }
                    }
                }
                if let Some(remainder) = remainder {
                    if let Some(variable) = variables.get(remainder.0 as usize) {
                        if variable.role != TheoryVariableRoleV1::Remainder {
                            errors.push(TheoryValidationError::InvalidVariableRole {
                                rule: owner.to_string(),
                                variable: variable.name.clone(),
                                expected: "Remainder",
                            });
                        }
                        require_equal_sort(owner, &node.sort, &variable.sort, errors);
                    } else {
                        errors.push(TheoryValidationError::UnknownVariable(remainder.0));
                    }
                }
            },
            TheoryTermFormV1::Map { collection, parameters, body } => {
                let collection = prior_term(owner, terms, index, *collection, errors);
                let body = prior_term(owner, terms, index, *body, errors);
                for parameter in parameters {
                    match variables.get(parameter.0 as usize) {
                        None => errors.push(TheoryValidationError::UnknownVariable(parameter.0)),
                        Some(variable) if variable.role != TheoryVariableRoleV1::Binder => {
                            errors.push(TheoryValidationError::InvalidVariableRole {
                                rule: owner.to_string(),
                                variable: variable.name.clone(),
                                expected: "Binder",
                            });
                        },
                        Some(_) => {},
                    }
                }
                if let (Some(collection), Some(body)) = (collection, body) {
                    let source_kind = sorts.get(collection.sort.as_str()).map(|sort| &sort.kind);
                    let target_kind = sorts.get(node.sort.as_str()).map(|sort| &sort.kind);
                    match (source_kind, target_kind) {
                        (
                            Some(TheorySortKindV1::Collection {
                                kind: source,
                                element: source_element,
                                ..
                            }),
                            Some(TheorySortKindV1::Collection { kind: target, element, .. }),
                        ) if source == target => {
                            require_equal_sort(owner, element, &body.sort, errors);
                            let expected_parameters = match sorts
                                .get(source_element.as_str())
                                .map(|sort| &sort.kind)
                            {
                                Some(TheorySortKindV1::Product { factors }) => factors.as_slice(),
                                _ => std::slice::from_ref(source_element),
                            };
                            if parameters.len() != expected_parameters.len() {
                                errors.push(TheoryValidationError::BindingArityMismatch {
                                    owner: owner.to_string(),
                                    expected: expected_parameters.len(),
                                    actual: parameters.len(),
                                });
                            }
                            for (parameter, expected) in parameters.iter().zip(expected_parameters)
                            {
                                if let Some(variable) = variables.get(parameter.0 as usize) {
                                    require_equal_sort(owner, expected, &variable.sort, errors);
                                }
                            }
                        },
                        _ => errors.push(TheoryValidationError::SortMismatch {
                            owner: owner.to_string(),
                            expected: format!("collection shaped like `{}`", collection.sort),
                            actual: node.sort.clone(),
                        }),
                    }
                }
            },
            TheoryTermFormV1::Zip { left, right } => {
                let left = prior_term(owner, terms, index, *left, errors);
                let right = prior_term(owner, terms, index, *right, errors);
                if let (Some(left), Some(right)) = (left, right) {
                    match sorts.get(node.sort.as_str()).map(|sort| &sort.kind) {
                        Some(TheorySortKindV1::Product { factors }) if factors.len() == 2 => {
                            require_equal_sort(owner, &factors[0], &left.sort, errors);
                            require_equal_sort(owner, &factors[1], &right.sort, errors);
                        },
                        _ => errors.push(TheoryValidationError::UnknownReference {
                            kind: "binary product sort",
                            name: node.sort.clone(),
                        }),
                    }
                }
            },
            TheoryTermFormV1::Literal(literal) => {
                let actual = literal_kind(literal);
                let expected = sorts
                    .get(node.sort.as_str())
                    .and_then(|sort| match &sort.kind {
                        TheorySortKindV1::Syntax { literal } => literal.as_ref(),
                        _ => None,
                    });
                if expected != Some(actual) {
                    errors.push(TheoryValidationError::SortMismatch {
                        owner: owner.to_string(),
                        expected: format!("{expected:?}"),
                        actual: format!("{actual:?}"),
                    });
                }
            },
        }
    }
}

fn validate_judgment_rule(
    owner: &JudgmentDeclV1,
    rule: &JudgmentRuleV1,
    sorts: &BTreeMap<&str, &TheorySortV1>,
    constructors: &BTreeMap<&str, &TheoryConstructorV1>,
    judgments: &BTreeMap<&str, &JudgmentDeclV1>,
    limits: TheoryLimitsV1,
    errors: &mut Vec<TheoryValidationError>,
) {
    let name = format!("{}::{}", owner.name, rule.name);
    if rule.conclusion.judgment != owner.name {
        errors.push(TheoryValidationError::JudgmentOwnerMismatch {
            rule: name.clone(),
            expected: owner.name.clone(),
            actual: rule.conclusion.judgment.clone(),
        });
    }
    validate_variables(&name, &rule.variables, sorts, limits, errors);
    validate_term_arena(&name, &rule.variables, &rule.terms, sorts, constructors, limits, errors);
    for atom in rule
        .premises
        .iter()
        .chain(std::iter::once(&rule.conclusion))
    {
        validate_judgment_atom(&name, atom, &rule.terms, judgments, errors);
    }
}

fn validate_judgment_atom(
    owner: &str,
    atom: &JudgmentAtomV1,
    terms: &[TheoryTermNodeV1],
    judgments: &BTreeMap<&str, &JudgmentDeclV1>,
    errors: &mut Vec<TheoryValidationError>,
) {
    let Some(judgment) = judgments.get(atom.judgment.as_str()) else {
        errors.push(TheoryValidationError::UnknownReference {
            kind: "judgment",
            name: atom.judgment.clone(),
        });
        return;
    };
    if atom.terms.len() != judgment.arguments.len() {
        errors.push(TheoryValidationError::ArityMismatch {
            constructor: atom.judgment.clone(),
            expected: judgment.arguments.len(),
            actual: atom.terms.len(),
        });
    }
    for (term, expected) in atom.terms.iter().zip(&judgment.arguments) {
        if let Some(node) = term_node(owner, terms, *term, errors) {
            require_equal_sort(owner, expected, &node.sort, errors);
        }
    }
}

fn validate_premise_dependencies(
    root: usize,
    validation: &PremiseValidationContext<'_>,
    available: &mut BTreeSet<TheoryVariableId>,
    premise_uses: &mut [u8],
    errors: &mut Vec<TheoryValidationError>,
) {
    let require_available = |variable: TheoryVariableId,
                             available: &BTreeSet<TheoryVariableId>,
                             errors: &mut Vec<TheoryValidationError>| {
        if !available.contains(&variable) {
            let name = validation
                .arena
                .variables
                .get(variable.0 as usize)
                .map(|value| value.name.clone())
                .unwrap_or_else(|| format!("#{}", variable.0));
            errors.push(TheoryValidationError::PremiseDependency {
                rule: validation.rule.to_string(),
                variable: name,
            });
        }
    };
    let mut work = vec![(root, available.clone(), true)];
    while let Some((index, mut scope, is_root)) = work.pop() {
        let Some(premise) = validation.arena.premises.get(index) else {
            errors.push(TheoryValidationError::UnknownPremise(index as u32));
            continue;
        };
        if let Some(uses) = premise_uses.get_mut(index) {
            *uses = uses.saturating_add(1);
            if *uses > 1 {
                errors.push(TheoryValidationError::SharedPremise(index as u32));
            }
        }
        match &premise.form {
            TheoryPremiseFormV1::Freshness { variable, target, .. } => {
                require_available(*variable, &scope, errors);
                require_available(*target, &scope, errors);
            },
            TheoryPremiseFormV1::Transition { source, target } => {
                if !validation.allow_transition {
                    errors.push(TheoryValidationError::TransitionInEquation(
                        validation.rule.to_string(),
                    ));
                }
                require_available(*source, &scope, errors);
                if scope.contains(target) {
                    let name = validation
                        .arena
                        .variables
                        .get(target.0 as usize)
                        .map(|value| value.name.clone())
                        .unwrap_or_else(|| format!("#{}", target.0));
                    errors.push(TheoryValidationError::PremiseDependency {
                        rule: validation.rule.to_string(),
                        variable: name,
                    });
                }
                if let Some(variable) = validation.arena.variables.get(target.0 as usize) {
                    if variable.role != TheoryVariableRoleV1::Derived {
                        errors.push(TheoryValidationError::InvalidVariableRole {
                            rule: validation.rule.to_string(),
                            variable: variable.name.clone(),
                            expected: "Derived",
                        });
                    }
                    if let Some(source) = validation.arena.variables.get(source.0 as usize) {
                        require_equal_sort(validation.rule, &source.sort, &variable.sort, errors);
                    }
                } else {
                    errors.push(TheoryValidationError::UnknownVariable(target.0));
                }
                if is_root {
                    available.insert(*target);
                }
            },
            TheoryPremiseFormV1::Judgment(atom) => {
                validate_judgment_atom(
                    validation.rule,
                    atom,
                    &validation.arena.terms,
                    validation.judgments,
                    errors,
                );
                for variable in atom.terms.iter().flat_map(|term| {
                    variable_occurrences(*term, &validation.arena.terms).into_keys()
                }) {
                    require_available(variable, &scope, errors);
                }
            },
            TheoryPremiseFormV1::ForAll { collection, parameter, body } => {
                require_available(*collection, &scope, errors);
                if body.0 as usize >= index {
                    errors.push(TheoryValidationError::NonTopologicalPremiseReference {
                        owner: index as u32,
                        target: body.0,
                    });
                }
                if let Some(parameter_decl) = validation.arena.variables.get(parameter.0 as usize) {
                    if parameter_decl.role != TheoryVariableRoleV1::Quantified {
                        errors.push(TheoryValidationError::InvalidVariableRole {
                            rule: validation.rule.to_string(),
                            variable: parameter_decl.name.clone(),
                            expected: "Quantified",
                        });
                    }
                    if let Some(collection_decl) =
                        validation.arena.variables.get(collection.0 as usize)
                    {
                        match validation
                            .sorts
                            .get(collection_decl.sort.as_str())
                            .map(|sort| &sort.kind)
                        {
                            Some(TheorySortKindV1::Collection { element, .. }) => {
                                require_equal_sort(
                                    validation.rule,
                                    element,
                                    &parameter_decl.sort,
                                    errors,
                                );
                            },
                            _ => errors.push(TheoryValidationError::UnknownReference {
                                kind: "forall collection sort",
                                name: collection_decl.sort.clone(),
                            }),
                        }
                    }
                    scope.insert(*parameter);
                } else {
                    errors.push(TheoryValidationError::UnknownVariable(parameter.0));
                }
                if validation.arena.premises.get(body.0 as usize).is_none() {
                    errors.push(TheoryValidationError::UnknownPremise(body.0));
                } else {
                    work.push((body.0 as usize, scope, false));
                }
            },
            TheoryPremiseFormV1::Guard(_) => {},
        }
    }
}

fn variable_occurrences(
    root: TheoryTermId,
    terms: &[TheoryTermNodeV1],
) -> BTreeMap<TheoryVariableId, u8> {
    let mut node_counts = vec![0u8; terms.len()];
    if let Some(count) = node_counts.get_mut(root.0 as usize) {
        *count = 1;
    }
    let mut variables = BTreeMap::new();
    for index in (0..terms.len()).rev() {
        let count = node_counts[index];
        if count == 0 {
            continue;
        }
        let mut add_variable = |variable: TheoryVariableId| {
            let occurrences = variables.entry(variable).or_insert(0u8);
            *occurrences = occurrences.saturating_add(count).min(2);
        };
        let mut add_child = |child: TheoryTermId| {
            if let Some(occurrences) = node_counts.get_mut(child.0 as usize) {
                *occurrences = occurrences.saturating_add(count).min(2);
            }
        };
        match &terms[index].form {
            TheoryTermFormV1::Variable(variable) => add_variable(*variable),
            TheoryTermFormV1::Constructor { arguments, .. } => {
                for child in arguments {
                    add_child(*child);
                }
            },
            TheoryTermFormV1::Abstraction { binder, body } => {
                add_variable(*binder);
                add_child(*body);
            },
            TheoryTermFormV1::Substitution { abstraction, argument } => {
                add_child(*abstraction);
                add_child(*argument);
            },
            TheoryTermFormV1::Collection { elements, remainder } => {
                for child in elements {
                    add_child(*child);
                }
                if let Some(remainder) = remainder {
                    add_variable(*remainder);
                }
            },
            TheoryTermFormV1::Map { collection, parameters, body } => {
                add_child(*collection);
                for parameter in parameters {
                    add_variable(*parameter);
                }
                add_child(*body);
            },
            TheoryTermFormV1::Zip { left, right } => {
                add_child(*left);
                add_child(*right);
            },
            TheoryTermFormV1::Literal(_) => {},
        }
    }
    variables
}

fn prior_term<'a>(
    owner: &str,
    terms: &'a [TheoryTermNodeV1],
    index: usize,
    term: TheoryTermId,
    errors: &mut Vec<TheoryValidationError>,
) -> Option<&'a TheoryTermNodeV1> {
    if term.0 as usize >= index {
        errors.push(TheoryValidationError::NonTopologicalTermReference {
            owner: index as u32,
            target: term.0,
        });
        return None;
    }
    term_node(owner, terms, term, errors)
}

fn term_node<'a>(
    _owner: &str,
    terms: &'a [TheoryTermNodeV1],
    term: TheoryTermId,
    errors: &mut Vec<TheoryValidationError>,
) -> Option<&'a TheoryTermNodeV1> {
    let node = terms.get(term.0 as usize);
    if node.is_none() {
        errors.push(TheoryValidationError::UnknownTerm(term.0));
    }
    node
}

fn require_equal_sort(
    owner: &str,
    expected: &str,
    actual: &str,
    errors: &mut Vec<TheoryValidationError>,
) {
    if expected != actual {
        errors.push(TheoryValidationError::SortMismatch {
            owner: owner.to_string(),
            expected: expected.to_string(),
            actual: actual.to_string(),
        });
    }
}

fn require_declared_sort(
    name: &str,
    sorts: &BTreeMap<&str, &TheorySortV1>,
    errors: &mut Vec<TheoryValidationError>,
) {
    if !sorts.contains_key(name) {
        errors
            .push(TheoryValidationError::UnknownReference { kind: "sort", name: name.to_string() });
    }
}

fn literal_kind(literal: &TheoryLiteralV1) -> &TheoryLiteralCarrierV1 {
    static STRING: TheoryLiteralCarrierV1 = TheoryLiteralCarrierV1::String;
    static BYTES: TheoryLiteralCarrierV1 = TheoryLiteralCarrierV1::Bytes;
    static INTEGER: TheoryLiteralCarrierV1 = TheoryLiteralCarrierV1::Integer;
    static FLOAT: TheoryLiteralCarrierV1 = TheoryLiteralCarrierV1::Float;
    static BOOLEAN: TheoryLiteralCarrierV1 = TheoryLiteralCarrierV1::Boolean;
    static UNIT: TheoryLiteralCarrierV1 = TheoryLiteralCarrierV1::Unit;
    match literal {
        TheoryLiteralV1::String(_) => &STRING,
        TheoryLiteralV1::Bytes(_) => &BYTES,
        TheoryLiteralV1::Integer(_) => &INTEGER,
        TheoryLiteralV1::FloatBits(_) => &FLOAT,
        TheoryLiteralV1::Boolean(_) => &BOOLEAN,
        TheoryLiteralV1::Unit => &UNIT,
    }
}

fn validate_limit(
    kind: &'static str,
    actual: usize,
    limit: u32,
    errors: &mut Vec<TheoryValidationError>,
) {
    if actual > limit as usize {
        errors.push(TheoryValidationError::LimitExceeded { kind, actual, limit });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structural_language_has_separate_stable_commitments() {
        let grammar = GrammarCoreV1::new("Guest");
        let language = LanguageCoreV1::structural(grammar);
        language.validate().expect("structural language is valid");
        assert_eq!(language.theory.profile, TheoryProfileV1::StructuralOnly);
        assert_ne!(language.grammar_fingerprint().unwrap(), language.theory_fingerprint().unwrap());
        assert_eq!(language.fingerprint().unwrap(), language.fingerprint().unwrap());
    }

    #[test]
    fn theory_presence_and_flat_term_topology_fail_closed() {
        let mut theory = TheoryCoreV1::structural();
        theory.profile = TheoryProfileV1::Oslf;
        theory.cost = Some(CostDeclV1 {
            base: "G".into(),
            signature_sort: "Sig".into(),
            stack_sort: "Stack".into(),
            wrapped_sort: "Wrapped".into(),
            located_sort: "Located".into(),
            product: "product".into(),
            unit: "unit".into(),
            rules: vec![],
            eta: "eta".into(),
            mu: "mu".into(),
            map: "map".into(),
            laws: vec![],
        });
        theory.sorts.push(TheorySortV1 {
            name: "Expr".into(),
            kind: TheorySortKindV1::Syntax { literal: None },
        });
        theory.constructors.push(TheoryConstructorV1 {
            name: "Loop".into(),
            domain: vec!["Expr".into()],
            codomain: "Expr".into(),
        });
        theory.equations.push(TheoryEquationV1 {
            name: "BadLoop".into(),
            arena: TheoryRuleArenaV1 {
                variables: Vec::new(),
                terms: vec![TheoryTermNodeV1 {
                    sort: "Expr".into(),
                    form: TheoryTermFormV1::Constructor {
                        constructor: "Loop".into(),
                        arguments: vec![TheoryTermId(0)],
                    },
                }],
                premises: Vec::new(),
                premise_roots: Vec::new(),
            },
            left: TheoryTermId(0),
            right: TheoryTermId(0),
        });
        let errors = LanguageCoreV1 {
            abi: LANGUAGE_CORE_ABI_V1,
            grammar: GrammarCoreV1::new("Guest"),
            theory,
        }
        .validate()
        .expect_err("invalid semantic structure must fail");
        assert!(errors.iter().any(|error| matches!(
            error,
            LanguageCoreValidationError::Theory(TheoryValidationError::CostRequiresContinued)
        )));
        assert!(errors.iter().any(|error| matches!(
            error,
            LanguageCoreValidationError::Theory(
                TheoryValidationError::NonTopologicalTermReference { owner: 0, target: 0 }
            )
        )));
    }

    #[test]
    fn forall_premise_scope_is_checked_iteratively_and_cannot_escape() {
        let sort_values = [
            TheorySortV1 {
                name: "Expr".into(),
                kind: TheorySortKindV1::Syntax { literal: None },
            },
            TheorySortV1 {
                name: "List(Expr)".into(),
                kind: TheorySortKindV1::Collection {
                    kind: crate::CollectionKind::List,
                    key: None,
                    element: "Expr".into(),
                },
            },
        ];
        let sorts: BTreeMap<_, _> = sort_values
            .iter()
            .map(|sort| (sort.name.as_str(), sort))
            .collect();
        let judgment_values = [JudgmentDeclV1 {
            name: "Holds".into(),
            arguments: vec!["Expr".into()],
            decision: JudgmentDecisionV1::Bounded,
            rules: Vec::new(),
        }];
        let judgments: BTreeMap<_, _> = judgment_values
            .iter()
            .map(|judgment| (judgment.name.as_str(), judgment))
            .collect();
        let constructors = BTreeMap::new();
        let validation = TheoryValidationContext {
            sorts: &sorts,
            constructors: &constructors,
            judgments: &judgments,
            limits: TheoryLimitsV1::default(),
        };
        let arena = TheoryRuleArenaV1 {
            variables: vec![
                TheoryVariableV1 {
                    id: TheoryVariableId(0),
                    name: "xs".into(),
                    sort: "List(Expr)".into(),
                    role: TheoryVariableRoleV1::Input,
                },
                TheoryVariableV1 {
                    id: TheoryVariableId(1),
                    name: "x".into(),
                    sort: "Expr".into(),
                    role: TheoryVariableRoleV1::Quantified,
                },
            ],
            terms: vec![
                TheoryTermNodeV1 {
                    sort: "Expr".into(),
                    form: TheoryTermFormV1::Variable(TheoryVariableId(1)),
                },
                TheoryTermNodeV1 {
                    sort: "List(Expr)".into(),
                    form: TheoryTermFormV1::Variable(TheoryVariableId(0)),
                },
            ],
            premises: vec![
                crate::TheoryPremiseNodeV1 {
                    form: TheoryPremiseFormV1::Judgment(JudgmentAtomV1 {
                        judgment: "Holds".into(),
                        terms: vec![TheoryTermId(0)],
                    }),
                },
                crate::TheoryPremiseNodeV1 {
                    form: TheoryPremiseFormV1::ForAll {
                        collection: TheoryVariableId(0),
                        parameter: TheoryVariableId(1),
                        body: crate::TheoryPremiseId(0),
                    },
                },
            ],
            premise_roots: vec![crate::TheoryPremiseId(1)],
        };
        let mut errors = Vec::new();
        validate_rule_arena(
            "EveryElement",
            &arena,
            TheoryTermId(1),
            TheoryTermId(1),
            true,
            &validation,
            &mut errors,
        );
        assert!(errors.is_empty(), "scoped premise must validate: {errors:?}");

        let mut escaping = Vec::new();
        validate_rule_arena(
            "EscapingElement",
            &arena,
            TheoryTermId(1),
            TheoryTermId(0),
            true,
            &validation,
            &mut escaping,
        );
        assert!(escaping.iter().any(|error| matches!(
            error,
            TheoryValidationError::UnboundVariable { variable, .. } if variable == "x"
        )));
    }
}
