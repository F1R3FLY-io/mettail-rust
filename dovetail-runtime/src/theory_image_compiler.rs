//! Checked compilation of runtime-defined GSLT rules into immutable semantic images.
//!
//! The compiler consumes the canonical, already-parsed [`LanguageCoreV1`]
//! directly.  It never reconstructs or reparses source text.  Rule arenas stay
//! flat, and positional left-hand sides enter Dovetail through its flat pattern
//! DAG API, so compilation is independent of the native call stack.

use dovetail::set_automaton::{
    AutomatonNode, FlatPattern, FlatPatternNode, FlatSetAutomatonError, PatternId, SetAutomaton,
};
use mettail_grammar_core::{
    theory_guard_commitment_v1, CollectionKind, LanguageCoreV1, SemanticActionV1, TheoryActionId,
    TheoryActionImageV1, TheoryConstructorId, TheoryConstructorImageV1, TheoryEffectId,
    TheoryGrammarConstructorV1, TheoryImageAdmissionLimits, TheoryImageError,
    TheoryImageOperatorV1, TheoryImagePremiseFormV1, TheoryImagePremiseNodeV1,
    TheoryImageTermFormV1, TheoryImageTermNodeV1, TheoryImageVariableV1, TheoryJudgmentId,
    TheoryPatternAutomatonV1, TheoryPatternEntryId, TheoryPatternEntryV1,
    TheoryPatternInvocationV1, TheoryPatternStateFormV1, TheoryPatternStateId,
    TheoryPatternStateV1, TheoryPremiseFormV1, TheoryRuleArenaV1, TheoryRuleDirectionV1,
    TheoryRuleDispositionV1, TheoryRuleOriginV1, TheoryRuleProgramId, TheoryRuleProgramV1,
    TheoryRuleReferenceV1, TheoryRuleSuppressionV1, TheorySemanticImageV1, TheorySortId,
    TheorySortKindV1, TheoryTermFormV1, TheoryTermId, TheoryVariableId, TheoryWorkChargeV1,
    THEORY_IMAGE_COMPILER_ABI_V1, THEORY_SEMANTIC_IMAGE_ABI_V1,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoryImageCompileError {
    Image(TheoryImageError),
    Automaton(FlatSetAutomatonError),
    NonProgressing { rule: String },
    UnknownReference { kind: &'static str, name: String },
    AmbiguousGrammarConstructor { name: String },
    EmptyActionTransition { action: String },
    InvalidAutomatonVariable { name: String },
    LengthOverflow,
    Allocation,
}

impl fmt::Display for TheoryImageCompileError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Image(error) => write!(formatter, "invalid semantic image: {error:?}"),
            Self::Automaton(error) => write!(formatter, "pattern automaton rejected: {error:?}"),
            Self::NonProgressing { rule } => {
                write!(formatter, "rule `{rule}` has identical left and right sides")
            },
            Self::UnknownReference { kind, name } => {
                write!(formatter, "unknown {kind} `{name}` during image compilation")
            },
            Self::AmbiguousGrammarConstructor { name } => write!(
                formatter,
                "theory constructor `{name}` maps to multiple grammar constructors"
            ),
            Self::EmptyActionTransition { action } => {
                write!(formatter, "action `{action}` has no executable transition")
            },
            Self::InvalidAutomatonVariable { name } => {
                write!(formatter, "invalid numeric automaton variable `{name}`")
            },
            Self::LengthOverflow => formatter.write_str("semantic image length overflow"),
            Self::Allocation => formatter.write_str("semantic image allocation failed"),
        }
    }
}

impl std::error::Error for TheoryImageCompileError {}

impl From<TheoryImageError> for TheoryImageCompileError {
    fn from(error: TheoryImageError) -> Self {
        Self::Image(error)
    }
}

impl From<FlatSetAutomatonError> for TheoryImageCompileError {
    fn from(error: FlatSetAutomatonError) -> Self {
        Self::Automaton(error)
    }
}

/// Compile one canonical language theory into a checked, fingerprint-bound,
/// authority-free execution image.
pub fn compile_theory_semantic_image(
    language: &LanguageCoreV1,
    limits: TheoryImageAdmissionLimits,
) -> Result<TheorySemanticImageV1, TheoryImageCompileError> {
    limits.validate_source(language)?;
    reject_non_progressing_rules(language)?;
    let context = CompileContext::new(language)?;
    let constructors = compile_constructors(language, &context)?;
    let rules = compile_rules(language, &context)?;
    let patterns = compile_patterns(&rules)?;
    let actions = compile_actions(&language.theory.actions, &rules, &context)?;
    let image = TheorySemanticImageV1 {
        abi: THEORY_SEMANTIC_IMAGE_ABI_V1,
        compiler_abi: THEORY_IMAGE_COMPILER_ABI_V1,
        language_fingerprint: language
            .fingerprint()
            .map_err(|error| TheoryImageError::Fingerprint(error.to_string()))?,
        grammar_fingerprint: language
            .grammar_fingerprint()
            .map_err(|error| TheoryImageError::Fingerprint(error.to_string()))?,
        theory_fingerprint: language
            .theory_fingerprint()
            .map_err(|error| TheoryImageError::Fingerprint(error.to_string()))?,
        constructors,
        rules,
        patterns,
        actions,
    };
    image.validate(language, limits)?;
    Ok(image)
}

struct CompileContext<'a> {
    language: &'a LanguageCoreV1,
    sorts: BTreeMap<&'a str, TheorySortId>,
    constructors: BTreeMap<&'a str, TheoryConstructorId>,
    judgments: BTreeMap<&'a str, TheoryJudgmentId>,
    effects: BTreeMap<&'a str, TheoryEffectId>,
}

impl<'a> CompileContext<'a> {
    fn new(language: &'a LanguageCoreV1) -> Result<Self, TheoryImageCompileError> {
        Ok(Self {
            language,
            sorts: dense_names(
                language.theory.sorts.iter().map(|sort| sort.name.as_str()),
                TheorySortId,
            )?,
            constructors: dense_names(
                language
                    .theory
                    .constructors
                    .iter()
                    .map(|constructor| constructor.name.as_str()),
                TheoryConstructorId,
            )?,
            judgments: dense_names(
                language
                    .theory
                    .judgments
                    .iter()
                    .map(|judgment| judgment.name.as_str()),
                TheoryJudgmentId,
            )?,
            effects: dense_names(
                language
                    .theory
                    .effects
                    .iter()
                    .map(|effect| effect.name.as_str()),
                TheoryEffectId,
            )?,
        })
    }

    fn sort(&self, name: &str) -> Result<TheorySortId, TheoryImageCompileError> {
        self.sorts
            .get(name)
            .copied()
            .ok_or_else(|| TheoryImageCompileError::UnknownReference {
                kind: "sort",
                name: name.to_string(),
            })
    }

    fn constructor(&self, name: &str) -> Result<TheoryConstructorId, TheoryImageCompileError> {
        self.constructors.get(name).copied().ok_or_else(|| {
            TheoryImageCompileError::UnknownReference {
                kind: "constructor",
                name: name.to_string(),
            }
        })
    }

    fn judgment(&self, name: &str) -> Result<TheoryJudgmentId, TheoryImageCompileError> {
        self.judgments
            .get(name)
            .copied()
            .ok_or_else(|| TheoryImageCompileError::UnknownReference {
                kind: "judgment",
                name: name.to_string(),
            })
    }

    fn effect(&self, name: &str) -> Result<TheoryEffectId, TheoryImageCompileError> {
        self.effects
            .get(name)
            .copied()
            .ok_or_else(|| TheoryImageCompileError::UnknownReference {
                kind: "effect",
                name: name.to_string(),
            })
    }

    fn collection(
        &self,
        sort: TheorySortId,
    ) -> Result<(TheorySortId, CollectionKind), TheoryImageCompileError> {
        let declaration = self
            .language
            .theory
            .sorts
            .get(sort.0 as usize)
            .ok_or_else(|| TheoryImageCompileError::UnknownReference {
                kind: "collection sort",
                name: format!("#{}", sort.0),
            })?;
        let TheorySortKindV1::Collection { kind, element, .. } = &declaration.kind else {
            return Err(TheoryImageCompileError::UnknownReference {
                kind: "collection sort",
                name: declaration.name.clone(),
            });
        };
        Ok((self.sort(element)?, *kind))
    }
}

fn dense_names<'a, Id>(
    names: impl IntoIterator<Item = &'a str>,
    wrap: fn(u32) -> Id,
) -> Result<BTreeMap<&'a str, Id>, TheoryImageCompileError> {
    let mut output = BTreeMap::new();
    for (index, name) in names.into_iter().enumerate() {
        let index = u32::try_from(index).map_err(|_| TheoryImageCompileError::LengthOverflow)?;
        output.insert(name, wrap(index));
    }
    Ok(output)
}

fn compile_constructors(
    language: &LanguageCoreV1,
    context: &CompileContext<'_>,
) -> Result<Vec<TheoryConstructorImageV1>, TheoryImageCompileError> {
    let mut output = empty_vec(language.theory.constructors.len())?;
    for (index, constructor) in language.theory.constructors.iter().enumerate() {
        let index = checked_u32(index)?;
        let mut domain = empty_vec(constructor.domain.len())?;
        for sort in &constructor.domain {
            domain.push(context.sort(sort)?);
        }
        output.push(TheoryConstructorImageV1 {
            id: TheoryConstructorId(index),
            domain,
            codomain: context.sort(&constructor.codomain)?,
            grammar: Some(unique_grammar_binding(language, &constructor.name)?),
        });
    }
    Ok(output)
}

fn unique_grammar_binding(
    language: &LanguageCoreV1,
    name: &str,
) -> Result<TheoryGrammarConstructorV1, TheoryImageCompileError> {
    let mut binding = None;
    for production in &language.grammar.productions {
        if production.label != name {
            continue;
        }
        let candidate = TheoryGrammarConstructorV1 {
            category: production.result,
            constructor: production.constructor,
        };
        if binding.is_some_and(|current| current != candidate) {
            return Err(TheoryImageCompileError::AmbiguousGrammarConstructor {
                name: name.to_string(),
            });
        }
        binding = Some(candidate);
    }
    binding.ok_or_else(|| TheoryImageCompileError::UnknownReference {
        kind: "grammar constructor",
        name: name.to_string(),
    })
}

fn compile_rules(
    language: &LanguageCoreV1,
    context: &CompileContext<'_>,
) -> Result<Vec<TheoryRuleProgramV1>, TheoryImageCompileError> {
    let count = language
        .theory
        .equations
        .len()
        .checked_mul(2)
        .and_then(|count| count.checked_add(language.theory.rewrites.len()))
        .ok_or(TheoryImageCompileError::LengthOverflow)?;
    let mut output = empty_vec(count)?;
    for (source, equation) in language.theory.equations.iter().enumerate() {
        let source = checked_u32(source)?;
        output.push(compile_rule(
            checked_program_id(output.len())?,
            TheoryRuleOriginV1::Equation {
                source,
                direction: TheoryRuleDirectionV1::Forward,
            },
            &equation.name,
            &equation.arena,
            equation.left,
            equation.right,
            false,
            context,
        )?);
        output.push(compile_rule(
            checked_program_id(output.len())?,
            TheoryRuleOriginV1::Equation {
                source,
                direction: TheoryRuleDirectionV1::Reverse,
            },
            &equation.name,
            &equation.arena,
            equation.right,
            equation.left,
            false,
            context,
        )?);
    }
    for (source, rewrite) in language.theory.rewrites.iter().enumerate() {
        output.push(compile_rule(
            checked_program_id(output.len())?,
            TheoryRuleOriginV1::Rewrite { source: checked_u32(source)? },
            &rewrite.name,
            &rewrite.arena,
            rewrite.left,
            rewrite.right,
            true,
            context,
        )?);
    }
    Ok(output)
}

#[allow(clippy::too_many_arguments)]
fn compile_rule(
    id: TheoryRuleProgramId,
    origin: TheoryRuleOriginV1,
    name: &str,
    arena: &TheoryRuleArenaV1,
    left: TheoryTermId,
    right: TheoryTermId,
    allow_transition: bool,
    context: &CompileContext<'_>,
) -> Result<TheoryRuleProgramV1, TheoryImageCompileError> {
    let mut variables = empty_vec(arena.variables.len())?;
    for variable in &arena.variables {
        variables.push(TheoryImageVariableV1 {
            id: variable.id,
            sort: context.sort(&variable.sort)?,
            role: variable.role,
        });
    }

    let mut terms = empty_vec(arena.terms.len())?;
    for term in &arena.terms {
        let sort = context.sort(&term.sort)?;
        let form = match &term.form {
            TheoryTermFormV1::Variable(variable) => TheoryImageTermFormV1::Slot(*variable),
            TheoryTermFormV1::Constructor { constructor, arguments } => {
                TheoryImageTermFormV1::Apply {
                    operator: TheoryImageOperatorV1::Constructor(context.constructor(constructor)?),
                    arguments: clone_vec(arguments)?,
                    slots: Vec::new(),
                    remainder: None,
                }
            },
            TheoryTermFormV1::Abstraction { binder, body } => TheoryImageTermFormV1::Apply {
                operator: TheoryImageOperatorV1::Abstraction { sort },
                arguments: vec![*body],
                slots: vec![*binder],
                remainder: None,
            },
            TheoryTermFormV1::Substitution { abstraction, argument } => {
                TheoryImageTermFormV1::Apply {
                    operator: TheoryImageOperatorV1::Substitution { sort },
                    arguments: vec![*abstraction, *argument],
                    slots: Vec::new(),
                    remainder: None,
                }
            },
            TheoryTermFormV1::Collection { elements, remainder } => {
                let (element, kind) = context.collection(sort)?;
                TheoryImageTermFormV1::Apply {
                    operator: TheoryImageOperatorV1::Collection { sort, element, kind },
                    arguments: clone_vec(elements)?,
                    slots: Vec::new(),
                    remainder: *remainder,
                }
            },
            TheoryTermFormV1::Map { collection, parameters, body } => {
                TheoryImageTermFormV1::Apply {
                    operator: TheoryImageOperatorV1::Map { sort },
                    arguments: vec![*collection, *body],
                    slots: clone_vec(parameters)?,
                    remainder: None,
                }
            },
            TheoryTermFormV1::Zip { left, right } => TheoryImageTermFormV1::Apply {
                operator: TheoryImageOperatorV1::Zip { sort },
                arguments: vec![*left, *right],
                slots: Vec::new(),
                remainder: None,
            },
            TheoryTermFormV1::Literal(value) => TheoryImageTermFormV1::Apply {
                operator: TheoryImageOperatorV1::Literal { sort, value: value.clone() },
                arguments: Vec::new(),
                slots: Vec::new(),
                remainder: None,
            },
        };
        terms.push(TheoryImageTermNodeV1 { sort, form });
    }

    let mut premises = empty_vec(arena.premises.len())?;
    for premise in &arena.premises {
        premises.push(TheoryImagePremiseNodeV1 {
            form: compile_premise(&premise.form, context)?,
        });
    }
    let mut premise_roots = empty_vec(arena.premise_roots.len())?;
    for root in &arena.premise_roots {
        premise_roots.push(root.0);
    }
    Ok(TheoryRuleProgramV1 {
        id,
        origin,
        disposition: compile_disposition(arena, left, right, allow_transition)?,
        name: name.to_string(),
        variables,
        terms,
        premises,
        premise_roots,
        left,
        right,
        charge: TheoryWorkChargeV1 {
            pattern_nodes: checked_u32(arena.terms.len())?,
            template_nodes: checked_u32(arena.terms.len())?,
            premise_nodes: checked_u32(arena.premises.len())?,
            variable_slots: checked_u32(arena.variables.len())?,
        },
    })
}

fn compile_premise(
    premise: &TheoryPremiseFormV1,
    context: &CompileContext<'_>,
) -> Result<TheoryImagePremiseFormV1, TheoryImageCompileError> {
    Ok(match premise {
        TheoryPremiseFormV1::Freshness { variable, target, remainder } => {
            TheoryImagePremiseFormV1::Freshness {
                variable: *variable,
                target: *target,
                remainder: *remainder,
            }
        },
        TheoryPremiseFormV1::Transition { source, target } => {
            TheoryImagePremiseFormV1::Transition { source: *source, target: *target }
        },
        TheoryPremiseFormV1::Judgment(atom) => TheoryImagePremiseFormV1::Judgment {
            judgment: context.judgment(&atom.judgment)?,
            terms: clone_vec(&atom.terms)?,
        },
        TheoryPremiseFormV1::ForAll { collection, parameter, body } => {
            TheoryImagePremiseFormV1::ForAll {
                collection: *collection,
                parameter: *parameter,
                body: body.0,
            }
        },
        TheoryPremiseFormV1::Guard(value) => TheoryImagePremiseFormV1::Guard {
            commitment: theory_guard_commitment_v1(value)?,
        },
    })
}

fn reject_non_progressing_rules(language: &LanguageCoreV1) -> Result<(), TheoryImageCompileError> {
    for equation in &language.theory.equations {
        if terms_equal(&equation.arena, equation.left, equation.right)? {
            return Err(TheoryImageCompileError::NonProgressing { rule: equation.name.clone() });
        }
    }
    for rewrite in &language.theory.rewrites {
        if terms_equal(&rewrite.arena, rewrite.left, rewrite.right)? {
            return Err(TheoryImageCompileError::NonProgressing { rule: rewrite.name.clone() });
        }
    }
    Ok(())
}

fn terms_equal(
    arena: &TheoryRuleArenaV1,
    left: TheoryTermId,
    right: TheoryTermId,
) -> Result<bool, TheoryImageCompileError> {
    let mut pending = vec![(left, right)];
    let mut visited = BTreeSet::new();
    while let Some((left, right)) = pending.pop() {
        if !visited.insert((left, right)) {
            continue;
        }
        let left_node = arena.terms.get(left.0 as usize).ok_or_else(|| {
            TheoryImageCompileError::UnknownReference {
                kind: "term",
                name: format!("#{}", left.0),
            }
        })?;
        let right_node = arena.terms.get(right.0 as usize).ok_or_else(|| {
            TheoryImageCompileError::UnknownReference {
                kind: "term",
                name: format!("#{}", right.0),
            }
        })?;
        if left_node.sort != right_node.sort {
            return Ok(false);
        }
        match (&left_node.form, &right_node.form) {
            (TheoryTermFormV1::Variable(left), TheoryTermFormV1::Variable(right))
                if left == right => {},
            (
                TheoryTermFormV1::Constructor {
                    constructor: left_constructor,
                    arguments: left_arguments,
                },
                TheoryTermFormV1::Constructor {
                    constructor: right_constructor,
                    arguments: right_arguments,
                },
            ) if left_constructor == right_constructor
                && left_arguments.len() == right_arguments.len() =>
            {
                pending.extend(
                    left_arguments
                        .iter()
                        .copied()
                        .zip(right_arguments.iter().copied()),
                );
            },
            (
                TheoryTermFormV1::Abstraction { binder: left_binder, body: left_body },
                TheoryTermFormV1::Abstraction { binder: right_binder, body: right_body },
            ) if left_binder == right_binder => pending.push((*left_body, *right_body)),
            (
                TheoryTermFormV1::Substitution {
                    abstraction: left_abstraction,
                    argument: left_argument,
                },
                TheoryTermFormV1::Substitution {
                    abstraction: right_abstraction,
                    argument: right_argument,
                },
            ) => {
                pending.push((*left_abstraction, *right_abstraction));
                pending.push((*left_argument, *right_argument));
            },
            (
                TheoryTermFormV1::Collection {
                    elements: left_elements,
                    remainder: left_remainder,
                },
                TheoryTermFormV1::Collection {
                    elements: right_elements,
                    remainder: right_remainder,
                },
            ) if left_remainder == right_remainder
                && left_elements.len() == right_elements.len() =>
            {
                pending.extend(
                    left_elements
                        .iter()
                        .copied()
                        .zip(right_elements.iter().copied()),
                );
            },
            (
                TheoryTermFormV1::Map {
                    collection: left_collection,
                    parameters: left_parameters,
                    body: left_body,
                },
                TheoryTermFormV1::Map {
                    collection: right_collection,
                    parameters: right_parameters,
                    body: right_body,
                },
            ) if left_parameters == right_parameters => {
                pending.push((*left_collection, *right_collection));
                pending.push((*left_body, *right_body));
            },
            (
                TheoryTermFormV1::Zip { left: left_first, right: left_second },
                TheoryTermFormV1::Zip { left: right_first, right: right_second },
            ) => {
                pending.push((*left_first, *right_first));
                pending.push((*left_second, *right_second));
            },
            (TheoryTermFormV1::Literal(left), TheoryTermFormV1::Literal(right))
                if left == right => {},
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn compile_disposition(
    arena: &TheoryRuleArenaV1,
    left: TheoryTermId,
    right: TheoryTermId,
    allow_transition: bool,
) -> Result<TheoryRuleDispositionV1, TheoryImageCompileError> {
    let root = arena.terms.get(left.0 as usize).ok_or_else(|| {
        TheoryImageCompileError::UnknownReference {
            kind: "left root",
            name: format!("#{}", left.0),
        }
    })?;
    if matches!(root.form, TheoryTermFormV1::Variable(_)) {
        return Ok(TheoryRuleDispositionV1::Suppressed(TheoryRuleSuppressionV1::MatchAllRoot));
    }
    let mut available = source_term_variables(arena, left)?;
    if let Some(variable) = first_unavailable_premise(arena, &mut available, allow_transition)? {
        return Ok(TheoryRuleDispositionV1::Suppressed(
            TheoryRuleSuppressionV1::PremiseDependency { variable },
        ));
    }
    if let Some(variable) = source_term_variables(arena, right)?
        .into_iter()
        .find(|variable| !available.contains(variable))
    {
        return Ok(TheoryRuleDispositionV1::Suppressed(TheoryRuleSuppressionV1::UnboundTemplate {
            variable,
        }));
    }
    Ok(TheoryRuleDispositionV1::Executable)
}

fn source_term_variables(
    arena: &TheoryRuleArenaV1,
    root: TheoryTermId,
) -> Result<BTreeSet<TheoryVariableId>, TheoryImageCompileError> {
    let mut variables = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        if !visited.insert(term) {
            continue;
        }
        let node = arena.terms.get(term.0 as usize).ok_or_else(|| {
            TheoryImageCompileError::UnknownReference {
                kind: "term",
                name: format!("#{}", term.0),
            }
        })?;
        match &node.form {
            TheoryTermFormV1::Variable(variable) => {
                variables.insert(*variable);
            },
            TheoryTermFormV1::Constructor { arguments, .. } => {
                pending.extend(arguments.iter().copied());
            },
            TheoryTermFormV1::Abstraction { binder, body } => {
                variables.insert(*binder);
                pending.push(*body);
            },
            TheoryTermFormV1::Substitution { abstraction, argument } => {
                pending.push(*abstraction);
                pending.push(*argument);
            },
            TheoryTermFormV1::Collection { elements, remainder } => {
                pending.extend(elements.iter().copied());
                variables.extend(remainder.iter().copied());
            },
            TheoryTermFormV1::Map { collection, parameters, body } => {
                pending.push(*collection);
                pending.push(*body);
                variables.extend(parameters.iter().copied());
            },
            TheoryTermFormV1::Zip { left, right } => {
                pending.push(*left);
                pending.push(*right);
            },
            TheoryTermFormV1::Literal(_) => {},
        }
    }
    Ok(variables)
}

fn first_unavailable_premise(
    arena: &TheoryRuleArenaV1,
    available: &mut BTreeSet<TheoryVariableId>,
    allow_transition: bool,
) -> Result<Option<TheoryVariableId>, TheoryImageCompileError> {
    for root in &arena.premise_roots {
        let mut pending = vec![(root.0, available.clone(), true)];
        while let Some((index, mut scope, is_root)) = pending.pop() {
            let premise = arena.premises.get(index as usize).ok_or_else(|| {
                TheoryImageCompileError::UnknownReference {
                    kind: "premise",
                    name: format!("#{index}"),
                }
            })?;
            let missing =
                |variable, scope: &BTreeSet<_>| (!scope.contains(&variable)).then_some(variable);
            match &premise.form {
                TheoryPremiseFormV1::Freshness { variable, target, .. } => {
                    if let Some(variable) =
                        missing(*variable, &scope).or_else(|| missing(*target, &scope))
                    {
                        return Ok(Some(variable));
                    }
                },
                TheoryPremiseFormV1::Transition { source, target } => {
                    if !allow_transition {
                        return Ok(Some(*source));
                    }
                    if let Some(variable) = missing(*source, &scope) {
                        return Ok(Some(variable));
                    }
                    if is_root {
                        available.insert(*target);
                    }
                },
                TheoryPremiseFormV1::Judgment(atom) => {
                    for term in &atom.terms {
                        if let Some(variable) = source_term_variables(arena, *term)?
                            .into_iter()
                            .find(|variable| !scope.contains(variable))
                        {
                            return Ok(Some(variable));
                        }
                    }
                },
                TheoryPremiseFormV1::ForAll { collection, parameter, body } => {
                    if let Some(variable) = missing(*collection, &scope) {
                        return Ok(Some(variable));
                    }
                    scope.insert(*parameter);
                    pending.push((body.0, scope, false));
                },
                TheoryPremiseFormV1::Guard(_) => {},
            }
        }
    }
    Ok(None)
}

fn compile_patterns(
    rules: &[TheoryRuleProgramV1],
) -> Result<TheoryPatternAutomatonV1, TheoryImageCompileError> {
    let mut source = empty_vec(rules.len())?;
    for rule in rules {
        if rule_is_positional(rule)? {
            source.push((PatternId(rule.id.0 as usize), flat_left_pattern(rule)?));
        }
    }
    let automaton = SetAutomaton::compile_structural_flat(source)?;
    let view = automaton.view();

    let mut states = empty_vec(view.state_count())?;
    for state in view.state_ids() {
        let id = TheoryPatternStateId(checked_u32(state.index())?);
        let slot_count = checked_u32(view.state_slot_count(state))?;
        let form = match view.node(state) {
            AutomatonNode::Var => TheoryPatternStateFormV1::Bind,
            AutomatonNode::App { op, args } => {
                let mut arguments = empty_vec(args.len())?;
                for invocation in args {
                    let mut parent_slots = empty_vec(invocation.slot_count())?;
                    for slot in invocation.parent_slots() {
                        parent_slots.push(checked_u32(slot.index())?);
                    }
                    arguments.push(TheoryPatternInvocationV1 {
                        state: TheoryPatternStateId(checked_u32(invocation.state().index())?),
                        parent_slots,
                    });
                }
                TheoryPatternStateFormV1::Apply { operator: op.clone(), arguments }
            },
        };
        states.push(TheoryPatternStateV1 { id, slot_count, form });
    }

    let mut entries = empty_vec(view.entry_count())?;
    for index in 0..view.entry_count() {
        let mut slot_variables = empty_vec(view.entry_slot_names(index).len())?;
        for name in view.entry_slot_names(index) {
            slot_variables.push(parse_automaton_variable(name)?);
        }
        entries.push(TheoryPatternEntryV1 {
            id: TheoryPatternEntryId(checked_u32(index)?),
            rule: TheoryRuleProgramId(checked_u32(view.entry_id(index).0)?),
            root: TheoryPatternStateId(checked_u32(view.entry_root_state(index).index())?),
            slot_variables,
        });
    }
    Ok(TheoryPatternAutomatonV1 { states, entries })
}

fn rule_is_positional(rule: &TheoryRuleProgramV1) -> Result<bool, TheoryImageCompileError> {
    if rule.disposition != TheoryRuleDispositionV1::Executable {
        return Ok(false);
    }
    let mut pending = vec![rule.left];
    let mut visited = BTreeSet::new();
    while let Some(term) = pending.pop() {
        if !visited.insert(term) {
            continue;
        }
        let node = rule.terms.get(term.0 as usize).ok_or_else(|| {
            TheoryImageCompileError::UnknownReference {
                kind: "pattern term",
                name: format!("#{}", term.0),
            }
        })?;
        if let TheoryImageTermFormV1::Apply { operator, arguments, remainder, .. } = &node.form {
            if remainder.is_some()
                || matches!(
                    operator,
                    TheoryImageOperatorV1::Collection {
                        kind: CollectionKind::Bag
                            | CollectionKind::Set
                            | CollectionKind::Map
                            | CollectionKind::PathMap,
                        ..
                    }
                )
            {
                return Ok(false);
            }
            pending.extend(arguments.iter().copied());
        }
    }
    Ok(true)
}

fn flat_left_pattern(
    rule: &TheoryRuleProgramV1,
) -> Result<FlatPattern<TheoryImageOperatorV1>, TheoryImageCompileError> {
    let mut reachable = vec![false; rule.terms.len()];
    let mut pending = vec![rule.left];
    while let Some(term) = pending.pop() {
        let node = rule.terms.get(term.0 as usize).ok_or_else(|| {
            TheoryImageCompileError::UnknownReference {
                kind: "pattern term",
                name: format!("#{}", term.0),
            }
        })?;
        if std::mem::replace(&mut reachable[term.0 as usize], true) {
            continue;
        }
        if let TheoryImageTermFormV1::Apply { arguments, .. } = &node.form {
            pending.extend(arguments.iter().copied());
        }
    }

    let reachable_count = reachable.iter().filter(|reachable| **reachable).count();
    let slot_count = rule
        .terms
        .iter()
        .zip(&reachable)
        .filter(|(_, reachable)| **reachable)
        .try_fold(0usize, |total, (term, _)| {
            let slots = match &term.form {
                TheoryImageTermFormV1::Slot(_) => 0,
                TheoryImageTermFormV1::Apply { slots, remainder, .. } => {
                    slots.len() + usize::from(remainder.is_some())
                },
            };
            total
                .checked_add(slots)
                .ok_or(TheoryImageCompileError::LengthOverflow)
        })?;
    let mut nodes = empty_vec(
        reachable_count
            .checked_add(slot_count)
            .ok_or(TheoryImageCompileError::LengthOverflow)?,
    )?;
    let mut translated = vec![None; rule.terms.len()];
    for (index, term) in rule.terms.iter().enumerate() {
        if !reachable[index] {
            continue;
        }
        let node = match &term.form {
            TheoryImageTermFormV1::Slot(variable) => {
                FlatPatternNode::Var(automaton_variable(*variable))
            },
            TheoryImageTermFormV1::Apply { operator, arguments, slots, remainder } => {
                if remainder.is_some() {
                    return Err(TheoryImageCompileError::UnknownReference {
                        kind: "positional collection remainder",
                        name: format!("rule#{}", rule.id.0),
                    });
                }
                let mut children = empty_vec(slots.len() + arguments.len())?;
                for variable in slots {
                    let child = nodes.len();
                    nodes.push(FlatPatternNode::Var(automaton_variable(*variable)));
                    children.push(child);
                }
                for argument in arguments {
                    children.push(translated[argument.0 as usize].ok_or_else(|| {
                        TheoryImageCompileError::UnknownReference {
                            kind: "backward pattern term",
                            name: format!("#{}", argument.0),
                        }
                    })?);
                }
                FlatPatternNode::App { op: operator.clone(), args: children }
            },
        };
        let target = nodes.len();
        nodes.push(node);
        translated[index] = Some(target);
    }
    let root = translated[rule.left.0 as usize].ok_or_else(|| {
        TheoryImageCompileError::UnknownReference {
            kind: "pattern root",
            name: format!("#{}", rule.left.0),
        }
    })?;
    Ok(FlatPattern { nodes, root })
}

fn automaton_variable(variable: TheoryVariableId) -> String {
    format!("v{}", variable.0)
}

fn parse_automaton_variable(name: &str) -> Result<TheoryVariableId, TheoryImageCompileError> {
    name.strip_prefix('v')
        .and_then(|digits| digits.parse::<u32>().ok())
        .map(TheoryVariableId)
        .ok_or_else(|| TheoryImageCompileError::InvalidAutomatonVariable { name: name.to_string() })
}

fn compile_actions(
    actions: &[SemanticActionV1],
    rules: &[TheoryRuleProgramV1],
    context: &CompileContext<'_>,
) -> Result<Vec<TheoryActionImageV1>, TheoryImageCompileError> {
    let mut output = empty_vec(actions.len())?;
    for (index, action) in actions.iter().enumerate() {
        if let TheoryRuleReferenceV1::Handler(name) = &action.transition {
            return Err(TheoryImageCompileError::UnknownReference {
                kind: "runtime handler",
                name: name.clone(),
            });
        }
        let transition_count = rules
            .iter()
            .filter(|rule| {
                action_names_rule(&action.transition, rule)
                    && rule.disposition == TheoryRuleDispositionV1::Executable
            })
            .count();
        let mut transitions = empty_vec(transition_count)?;
        for rule in rules {
            if action_names_rule(&action.transition, rule)
                && rule.disposition == TheoryRuleDispositionV1::Executable
            {
                transitions.push(rule.id);
            }
        }
        if transitions.is_empty() {
            return Err(TheoryImageCompileError::EmptyActionTransition {
                action: action.id.clone(),
            });
        }
        let mut domain = empty_vec(action.domain.len())?;
        for sort in &action.domain {
            domain.push(context.sort(sort)?);
        }
        output.push(TheoryActionImageV1 {
            id: TheoryActionId(checked_u32(index)?),
            domain,
            codomain: context.sort(&action.codomain)?,
            transitions,
            effect: context.effect(&action.effect)?,
            effect_class: action.effect_class,
            required_rights: action.required_rights.clone(),
            grade: context.sort(&action.grade)?,
        });
    }
    Ok(output)
}

fn action_names_rule(reference: &TheoryRuleReferenceV1, rule: &TheoryRuleProgramV1) -> bool {
    match (reference, rule.origin) {
        (TheoryRuleReferenceV1::Equation(name), TheoryRuleOriginV1::Equation { .. })
        | (TheoryRuleReferenceV1::Rewrite(name), TheoryRuleOriginV1::Rewrite { .. }) => {
            rule.name == *name
        },
        (TheoryRuleReferenceV1::Handler(_), _) => false,
        _ => false,
    }
}

fn checked_program_id(index: usize) -> Result<TheoryRuleProgramId, TheoryImageCompileError> {
    Ok(TheoryRuleProgramId(checked_u32(index)?))
}

fn checked_u32(value: usize) -> Result<u32, TheoryImageCompileError> {
    u32::try_from(value).map_err(|_| TheoryImageCompileError::LengthOverflow)
}

fn empty_vec<T>(capacity: usize) -> Result<Vec<T>, TheoryImageCompileError> {
    let mut output = Vec::new();
    output
        .try_reserve_exact(capacity)
        .map_err(|_| TheoryImageCompileError::Allocation)?;
    Ok(output)
}

fn clone_vec<T: Clone>(source: &[T]) -> Result<Vec<T>, TheoryImageCompileError> {
    let mut output = empty_vec(source.len())?;
    output.extend_from_slice(source);
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_grammar_core::{
        Associativity, Carrier, Category, CategoryId, ConstructorId, EffectDeclV1, FieldSource,
        GrammarCoreV1, LanguageRight, LanguageRights, Precedence, Production, ProductionClass,
        ProductionId, ReductionPlan, SemanticEffectClassV1, SyntaxItem, TheoryConstructorV1,
        TheoryEquationV1, TheoryPremiseId, TheoryPremiseNodeV1, TheoryProfileV1, TheoryRewriteV1,
        TheorySortV1, TheoryTermNodeV1, TheoryVariableRoleV1, TheoryVariableV1,
        LANGUAGE_CORE_ABI_V1,
    };

    fn production(
        id: u32,
        label: &str,
        syntax: Vec<SyntaxItem>,
        fields: Vec<FieldSource>,
    ) -> (Production, ReductionPlan) {
        let input_arity = u16::try_from(fields.len()).expect("small fixture arity");
        (
            Production {
                id: ProductionId(id),
                constructor: ConstructorId(id),
                label: label.into(),
                result: CategoryId(0),
                syntax,
                precedence: Precedence {
                    binding_power: None,
                    associativity: Associativity::NonAssociative,
                    shares_previous_level: false,
                },
                classification: ProductionClass::default(),
                reduction: id,
                provenance: None,
            },
            ReductionPlan {
                output_category: CategoryId(0),
                constructor: ConstructorId(id),
                input_arity,
                fields,
                evaluation: None,
                evaluation_mode: None,
                tier: None,
            },
        )
    }

    fn term_variable(id: u32) -> TheoryTermNodeV1 {
        TheoryTermNodeV1 {
            sort: "Expr".into(),
            form: TheoryTermFormV1::Variable(TheoryVariableId(id)),
        }
    }

    fn term_constructor(name: &str, arguments: Vec<TheoryTermId>) -> TheoryTermNodeV1 {
        TheoryTermNodeV1 {
            sort: "Expr".into(),
            form: TheoryTermFormV1::Constructor { constructor: name.into(), arguments },
        }
    }

    fn variable(id: u32, name: &str) -> TheoryVariableV1 {
        TheoryVariableV1 {
            id: TheoryVariableId(id),
            name: name.into(),
            sort: "Expr".into(),
            role: TheoryVariableRoleV1::Input,
        }
    }

    fn fixture() -> LanguageCoreV1 {
        let mut grammar = GrammarCoreV1::new("TheoryFixture");
        grammar.categories.push(Category {
            id: CategoryId(0),
            name: "Expr".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: true,
        });
        let specifications = [
            production(0, "Zero", Vec::new(), Vec::new()),
            production(
                1,
                "Wrap",
                vec![SyntaxItem::Category {
                    category: CategoryId(0),
                    slot: "value".into(),
                }],
                vec![FieldSource::Input(0)],
            ),
            production(
                2,
                "Add",
                vec![
                    SyntaxItem::Category {
                        category: CategoryId(0),
                        slot: "left".into(),
                    },
                    SyntaxItem::Category {
                        category: CategoryId(0),
                        slot: "right".into(),
                    },
                ],
                vec![FieldSource::Input(0), FieldSource::Input(1)],
            ),
        ];
        for (production, reduction) in specifications {
            grammar.productions.push(production);
            grammar.reductions.push(reduction);
        }

        let commutative = TheoryRuleArenaV1 {
            variables: vec![variable(0, "x"), variable(1, "y")],
            terms: vec![
                term_variable(0),
                term_variable(1),
                term_constructor("Add", vec![TheoryTermId(0), TheoryTermId(1)]),
                term_constructor("Add", vec![TheoryTermId(1), TheoryTermId(0)]),
            ],
            premises: Vec::new(),
            premise_roots: Vec::new(),
        };
        let add_zero = TheoryRuleArenaV1 {
            variables: vec![variable(0, "x")],
            terms: vec![
                term_variable(0),
                term_constructor("Zero", Vec::new()),
                term_constructor("Add", vec![TheoryTermId(1), TheoryTermId(0)]),
            ],
            premises: Vec::new(),
            premise_roots: Vec::new(),
        };

        let mut theory = mettail_grammar_core::TheoryCoreV1::structural();
        theory.profile = TheoryProfileV1::Oslf;
        theory.sorts.push(TheorySortV1 {
            name: "Expr".into(),
            kind: TheorySortKindV1::Syntax { literal: None },
        });
        theory.constructors = vec![
            TheoryConstructorV1 {
                name: "Zero".into(),
                domain: Vec::new(),
                codomain: "Expr".into(),
            },
            TheoryConstructorV1 {
                name: "Wrap".into(),
                domain: vec!["Expr".into()],
                codomain: "Expr".into(),
            },
            TheoryConstructorV1 {
                name: "Add".into(),
                domain: vec!["Expr".into(), "Expr".into()],
                codomain: "Expr".into(),
            },
        ];
        theory.equations.push(TheoryEquationV1 {
            name: "commutative".into(),
            arena: commutative,
            left: TheoryTermId(2),
            right: TheoryTermId(3),
        });
        theory.rewrites.push(TheoryRewriteV1 {
            name: "add-zero".into(),
            arena: add_zero,
            left: TheoryTermId(2),
            right: TheoryTermId(0),
        });
        theory.effects.push(EffectDeclV1 {
            name: "pure".into(),
            class: SemanticEffectClassV1::Pure,
            requires: Vec::new(),
            emits: Vec::new(),
        });
        theory.actions.push(SemanticActionV1 {
            id: "reduce-add-zero".into(),
            domain: vec!["Expr".into()],
            codomain: "Expr".into(),
            transition: TheoryRuleReferenceV1::Rewrite("add-zero".into()),
            effect: "pure".into(),
            effect_class: SemanticEffectClassV1::Pure,
            required_rights: LanguageRights::from_rights([LanguageRight::Reduce]),
            grade: "Expr".into(),
        });
        LanguageCoreV1 {
            abi: LANGUAGE_CORE_ABI_V1,
            grammar,
            theory,
        }
    }

    #[test]
    fn canonical_rules_compile_deterministically_to_checked_images() {
        let language = fixture();
        language.validate().expect("fixture language");
        let limits = TheoryImageAdmissionLimits::default();
        let first = compile_theory_semantic_image(&language, limits).expect("compile image");
        let second = compile_theory_semantic_image(&language, limits).expect("compile image again");
        assert_eq!(first, second);
        assert_eq!(first.rules.len(), 3);
        assert_eq!(first.patterns.entries.len(), 3);
        assert_eq!(first.actions[0].transitions, vec![TheoryRuleProgramId(2)]);
        assert_eq!(
            first.actions[0].required_rights,
            LanguageRights::from_rights([LanguageRight::Reduce])
        );
        first
            .validate(&language, limits)
            .expect("independent image validation");
    }

    #[test]
    fn unsafe_reverse_orientation_is_retained_but_not_executable() {
        let mut language = fixture();
        let arena = TheoryRuleArenaV1 {
            variables: vec![variable(0, "x"), variable(1, "y")],
            terms: vec![
                term_variable(0),
                term_variable(1),
                term_constructor("Add", vec![TheoryTermId(0), TheoryTermId(1)]),
                term_constructor("Wrap", vec![TheoryTermId(0)]),
            ],
            premises: Vec::new(),
            premise_roots: Vec::new(),
        };
        language.theory.equations[0] = TheoryEquationV1 {
            name: "projection".into(),
            arena,
            left: TheoryTermId(2),
            right: TheoryTermId(3),
        };
        let image = compile_theory_semantic_image(&language, TheoryImageAdmissionLimits::default())
            .expect("compile image");
        assert_eq!(image.rules[0].disposition, TheoryRuleDispositionV1::Executable);
        assert_eq!(
            image.rules[1].disposition,
            TheoryRuleDispositionV1::Suppressed(TheoryRuleSuppressionV1::UnboundTemplate {
                variable: TheoryVariableId(1),
            },)
        );
        assert_eq!(image.patterns.entries.len(), 2);
    }

    #[test]
    fn source_limits_and_structurally_non_progressing_rules_fail_closed() {
        let language = fixture();
        let limits = TheoryImageAdmissionLimits {
            max_total_term_nodes: 1,
            ..TheoryImageAdmissionLimits::default()
        };
        assert!(matches!(
            compile_theory_semantic_image(&language, limits),
            Err(TheoryImageCompileError::Image(TheoryImageError::LimitExceeded("term nodes")))
        ));
        let limits = TheoryImageAdmissionLimits {
            max_total_constructor_arguments: 1,
            ..TheoryImageAdmissionLimits::default()
        };
        assert!(matches!(
            compile_theory_semantic_image(&language, limits),
            Err(TheoryImageCompileError::Image(TheoryImageError::LimitExceeded(
                "constructor arguments"
            )))
        ));
        let limits = TheoryImageAdmissionLimits {
            max_automaton_slot_references: 1,
            ..TheoryImageAdmissionLimits::default()
        };
        assert!(matches!(
            compile_theory_semantic_image(&language, limits),
            Err(TheoryImageCompileError::Image(TheoryImageError::LimitExceeded(
                "automaton slot references"
            )))
        ));

        let mut language = fixture();
        let arena = TheoryRuleArenaV1 {
            variables: vec![variable(0, "x")],
            terms: vec![
                term_variable(0),
                term_constructor("Zero", Vec::new()),
                term_constructor("Add", vec![TheoryTermId(1), TheoryTermId(0)]),
                term_constructor("Zero", Vec::new()),
                term_constructor("Add", vec![TheoryTermId(3), TheoryTermId(0)]),
            ],
            premises: Vec::new(),
            premise_roots: Vec::new(),
        };
        language.theory.rewrites[0] = TheoryRewriteV1 {
            name: "duplicate-shape".into(),
            arena,
            left: TheoryTermId(2),
            right: TheoryTermId(4),
        };
        language.theory.actions[0].transition =
            TheoryRuleReferenceV1::Rewrite("duplicate-shape".into());
        assert_eq!(
            compile_theory_semantic_image(&language, TheoryImageAdmissionLimits::default(),),
            Err(TheoryImageCompileError::NonProgressing { rule: "duplicate-shape".into() })
        );
    }

    #[test]
    fn bounded_wire_codec_round_trips_and_rejects_untrusted_lengths() {
        let language = fixture();
        let limits = TheoryImageAdmissionLimits::default();
        let image = compile_theory_semantic_image(&language, limits).expect("compile image");
        let bytes = image.encode(&language, limits).expect("encode image");
        let decoded = TheorySemanticImageV1::decode(&bytes, &language, limits)
            .expect("decode admitted image");
        assert_eq!(decoded, image);
        assert_eq!(decoded.fingerprint().unwrap(), image.fingerprint().unwrap());

        let mut forged_count = bytes.clone();
        let constructor_count_offset = 8 + 2 + 2 + 32 + 32 + 32;
        forged_count[constructor_count_offset..constructor_count_offset + 4]
            .copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(matches!(
            TheorySemanticImageV1::decode(&forged_count, &language, limits),
            Err(TheoryImageError::SourceMismatch { kind: "constructor count", .. })
        ));

        let mut forged_fingerprint = bytes.clone();
        forged_fingerprint[12] ^= 1;
        assert!(matches!(
            TheorySemanticImageV1::decode(&forged_fingerprint, &language, limits),
            Err(TheoryImageError::FingerprintMismatch("language"))
        ));
        assert_eq!(
            TheorySemanticImageV1::decode(&bytes[..bytes.len() - 1], &language, limits),
            Err(TheoryImageError::Truncated)
        );
    }

    #[test]
    fn rewrite_transition_premises_compile_as_ordered_continuations() {
        let mut language = fixture();
        language.theory.rewrites[0] = TheoryRewriteV1 {
            name: "step".into(),
            arena: TheoryRuleArenaV1 {
                variables: vec![
                    variable(0, "source"),
                    TheoryVariableV1 {
                        id: TheoryVariableId(1),
                        name: "target".into(),
                        sort: "Expr".into(),
                        role: TheoryVariableRoleV1::Derived,
                    },
                ],
                terms: vec![
                    term_variable(0),
                    term_variable(1),
                    term_constructor("Wrap", vec![TheoryTermId(0)]),
                ],
                premises: vec![TheoryPremiseNodeV1 {
                    form: TheoryPremiseFormV1::Transition {
                        source: TheoryVariableId(0),
                        target: TheoryVariableId(1),
                    },
                }],
                premise_roots: vec![TheoryPremiseId(0)],
            },
            left: TheoryTermId(2),
            right: TheoryTermId(1),
        };
        language.theory.actions[0].transition = TheoryRuleReferenceV1::Rewrite("step".into());
        let image = compile_theory_semantic_image(&language, TheoryImageAdmissionLimits::default())
            .expect("compile transition rule");
        let rule = &image.rules[2];
        assert_eq!(rule.premise_roots, vec![0]);
        assert_eq!(
            rule.premises[0].form,
            TheoryImagePremiseFormV1::Transition {
                source: TheoryVariableId(0),
                target: TheoryVariableId(1),
            }
        );
        assert_eq!(rule.disposition, TheoryRuleDispositionV1::Executable);
    }

    #[test]
    fn generalized_collection_rules_remain_complete_outside_positional_automaton() {
        let mut language = fixture();
        language.theory.sorts.push(TheorySortV1 {
            name: "SetExpr".into(),
            kind: TheorySortKindV1::Collection {
                kind: CollectionKind::Set,
                key: None,
                element: "Expr".into(),
            },
        });
        language.theory.rewrites.push(TheoryRewriteV1 {
            name: "drop-second".into(),
            arena: TheoryRuleArenaV1 {
                variables: vec![variable(0, "x"), variable(1, "y")],
                terms: vec![
                    term_variable(0),
                    term_variable(1),
                    TheoryTermNodeV1 {
                        sort: "SetExpr".into(),
                        form: TheoryTermFormV1::Collection {
                            elements: vec![TheoryTermId(0), TheoryTermId(1)],
                            remainder: None,
                        },
                    },
                    TheoryTermNodeV1 {
                        sort: "SetExpr".into(),
                        form: TheoryTermFormV1::Collection {
                            elements: vec![TheoryTermId(0)],
                            remainder: None,
                        },
                    },
                ],
                premises: Vec::new(),
                premise_roots: Vec::new(),
            },
            left: TheoryTermId(2),
            right: TheoryTermId(3),
        });
        let image = compile_theory_semantic_image(&language, TheoryImageAdmissionLimits::default())
            .expect("compile generalized rule");
        assert_eq!(image.rules.len(), 4);
        assert_eq!(image.rules[3].disposition, TheoryRuleDispositionV1::Executable);
        assert!(image
            .patterns
            .entries
            .iter()
            .all(|entry| entry.rule != TheoryRuleProgramId(3)));
        image
            .validate(&language, TheoryImageAdmissionLimits::default())
            .expect("complete non-positional program validates");
    }

    #[test]
    fn independent_validator_rejects_tampered_automaton_structure() {
        let language = fixture();
        let limits = TheoryImageAdmissionLimits::default();
        let mut image = compile_theory_semantic_image(&language, limits).expect("compile image");
        let state = image
            .patterns
            .states
            .iter_mut()
            .find(|state| matches!(state.form, TheoryPatternStateFormV1::Apply { .. }))
            .expect("application state");
        if let TheoryPatternStateFormV1::Apply { operator, .. } = &mut state.form {
            *operator = TheoryImageOperatorV1::Constructor(TheoryConstructorId(u32::MAX));
        }
        assert!(matches!(
            image.validate(&language, limits),
            Err(TheoryImageError::AutomatonShape { .. })
        ));
    }

    #[test]
    fn deeply_nested_rule_compilation_is_stack_safe() {
        const DEPTH: u32 = 20_000;
        let mut language = fixture();
        let mut terms = Vec::with_capacity(DEPTH as usize + 1);
        terms.push(term_variable(0));
        for index in 0..DEPTH {
            terms.push(term_constructor("Wrap", vec![TheoryTermId(index)]));
        }
        language.theory.rewrites[0] = TheoryRewriteV1 {
            name: "unwrap-deep".into(),
            arena: TheoryRuleArenaV1 {
                variables: vec![variable(0, "x")],
                terms,
                premises: Vec::new(),
                premise_roots: Vec::new(),
            },
            left: TheoryTermId(DEPTH),
            right: TheoryTermId(0),
        };
        language.theory.actions[0].transition =
            TheoryRuleReferenceV1::Rewrite("unwrap-deep".into());
        let image = compile_theory_semantic_image(&language, TheoryImageAdmissionLimits::default())
            .expect("compile deep flat rule");
        assert_eq!(image.rules[2].terms.len(), DEPTH as usize + 1);
    }
}
