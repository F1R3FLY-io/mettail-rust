//! Complete source-neutral language artifacts.
//!
//! [`GrammarCoreV1`] is deliberately only the recognition/construction
//! projection. [`TheoryCoreV1`] carries dynamics, OSLF judgments, effects,
//! interaction/continuation witnesses, `Cost(G)`, and host resource projection.
//! Keeping the two projections separate lets a parser image remain reusable
//! when only semantic theory changes, while [`LanguageCoreV1::fingerprint`]
//! binds both projections for authority, FLTs, theorem channels, and replay.

use crate::{GrammarCoreV1, ValidationError};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

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
    /// A topologically ordered, flat term arena. Constructor arguments must
    /// point strictly backward, so validation and evaluation never recurse.
    pub terms: Vec<TheoryTermNodeV1>,
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
            terms: Vec::new(),
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
        if self.terms.len() > self.limits.max_term_nodes as usize {
            errors.push(TheoryValidationError::TermLimitExceeded {
                actual: self.terms.len(),
                limit: self.limits.max_term_nodes,
            });
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

        let mut sorts: BTreeSet<&str> = grammar
            .categories
            .iter()
            .map(|category| category.name.as_str())
            .collect();
        sorts.extend(self.sorts.iter().map(|sort| sort.name.as_str()));
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
        let judgments: BTreeSet<&str> = self
            .judgments
            .iter()
            .map(|judgment| judgment.name.as_str())
            .collect();

        for (index, node) in self.terms.iter().enumerate() {
            if let TheoryTermNodeV1::Constructor { arguments, .. } = node {
                for argument in arguments {
                    if argument.0 as usize >= index {
                        errors.push(TheoryValidationError::NonTopologicalTermReference {
                            owner: index as u32,
                            target: argument.0,
                        });
                    }
                }
            }
        }
        for action in &self.actions {
            require_sorts(action.domain.iter().map(String::as_str), &sorts, &mut errors);
            require_sort(&action.codomain, &sorts, &mut errors);
            require_sort(&action.grade, &sorts, &mut errors);
            if !effects.contains(action.effect.as_str()) {
                errors.push(TheoryValidationError::UnknownReference {
                    kind: "effect",
                    name: action.effect.clone(),
                });
            }
        }
        for judgment in &self.judgments {
            require_sorts(judgment.arguments.iter().map(String::as_str), &sorts, &mut errors);
            for rule in &judgment.rules {
                for atom in rule
                    .premises
                    .iter()
                    .chain(std::iter::once(&rule.conclusion))
                {
                    if !judgments.contains(atom.judgment.as_str()) {
                        errors.push(TheoryValidationError::UnknownReference {
                            kind: "judgment",
                            name: atom.judgment.clone(),
                        });
                    }
                    for term in &atom.terms {
                        if term.0 as usize >= self.terms.len() {
                            errors.push(TheoryValidationError::UnknownTerm(term.0));
                        }
                    }
                }
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
        errors
    }

    fn has_semantic_structure(&self) -> bool {
        !self.sorts.is_empty()
            || !self.constructors.is_empty()
            || !self.binders.is_empty()
            || !self.terms.is_empty()
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
    pub bound_sort: String,
    pub body_sort: String,
    pub result_sort: String,
    pub multiple: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TheoryTermId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryTermNodeV1 {
    Variable(String),
    Constructor {
        constructor: String,
        arguments: Vec<TheoryTermId>,
    },
    Literal(TheoryLiteralV1),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryLiteralV1 {
    String(String),
    Bytes(Vec<u8>),
    Integer(i128),
    FloatBits(u64),
    Boolean(bool),
    Unit,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticActionV1 {
    pub id: String,
    pub domain: Vec<String>,
    pub codomain: String,
    pub transition: TheoryRuleReferenceV1,
    pub effect: String,
    pub grade: String,
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
pub struct JudgmentRuleV1 {
    pub name: String,
    pub premises: Vec<JudgmentAtomV1>,
    pub conclusion: JudgmentAtomV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JudgmentAtomV1 {
    pub judgment: String,
    pub terms: Vec<TheoryTermId>,
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
    pub max_term_nodes: u32,
    pub max_proof_nodes: u32,
    pub max_frontier: u32,
    pub max_steps: u32,
    pub max_grade_bits: u32,
}

impl TheoryLimitsV1 {
    fn has_zero_bound(self) -> bool {
        self.max_term_nodes == 0
            || self.max_proof_nodes == 0
            || self.max_frontier == 0
            || self.max_steps == 0
            || self.max_grade_bits == 0
    }
}

impl Default for TheoryLimitsV1 {
    fn default() -> Self {
        Self {
            max_term_nodes: 1_000_000,
            max_proof_nodes: 1_000_000,
            max_frontier: 100_000,
            max_steps: 10_000_000,
            max_grade_bits: 4096,
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
    TermLimitExceeded { actual: usize, limit: u32 },
    StructuralProfileContainsOslfData,
    ContinuedRequiresInteractive,
    CostRequiresContinued,
    DuplicateName { kind: &'static str, name: String },
    UnknownReference { kind: &'static str, name: String },
    UnknownTerm(u32),
    NonTopologicalTermReference { owner: u32, target: u32 },
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
        theory.terms.push(TheoryTermNodeV1::Constructor {
            constructor: "Loop".into(),
            arguments: vec![TheoryTermId(0)],
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
}
