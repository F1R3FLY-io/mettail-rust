//! Installed runtime composition of the original descriptor and WPDA workers.
//!
//! Installation owns the derived descriptor artifact once. Each parse borrows
//! its already-authorized lexical session, adapts its lattice without lexing
//! again, and runs the original walker. Publication requires complete bounded
//! realization of every accepting root; there is no legacy recognizer fallback.

use super::{
    absorption::derive_absorption_rows_admitted,
    actions::{OwnedActionProvider, OwnedTerm},
    backend_admission::PreparationBudget,
    engine::{AbsorptionRows, OwnedWpdaEngine},
    source::{OwnedTokenSource, SourceAdapterLimits},
};
use crate::runtime_backend::{RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI};
use crate::wpda_rule_analysis::{
    authored_action::authored_action_categories_admitted,
    authored_descriptors::{
        derive_authored_descriptors_admitted, DescriptorOptions, OwnedWpdaDescriptors,
    },
    authored_synthesis::{derive_authored_rules_admitted, AuthoredSynthesisOutput},
};
use crate::wpda_runtime::{ActionInvocationError, RealizationError, WpdaResolveResult};
use crate::wpda_walker::{WalkerResourceError, WalkerResourceLimits, WpdaWalker};
use mettail_grammar_core::{
    CategoryId, KeywordReservation, ParseWeight, ParserImageAdmissionLimits, RuntimeError,
    RuntimeLexicalSession, RuntimeParserAdmission, RuntimeParserBackend, RuntimeParserFactory,
    RuntimePolicy, WeightedParse,
};
use std::sync::Arc;

#[derive(Debug, Default)]
pub struct SharedWpdaRuntimeFactory;

struct PreparedBackend {
    descriptors: OwnedWpdaDescriptors<()>,
    absorption: AbsorptionRows,
    categories: Vec<CategoryId>,
    primary: CategoryId,
    contextual_keywords: Vec<String>,
    admission: ParserImageAdmissionLimits,
}

fn preparation_error(error: impl std::fmt::Debug) -> RuntimeError {
    RuntimeError::Image(format!("shared WPDA preparation: {error:?}"))
}

impl RuntimeParserFactory for SharedWpdaRuntimeFactory {
    fn semantic_commitment(&self) -> [u8; 32] {
        *blake3::hash(b"mettail-original-wpda-installed-backend/1").as_bytes()
    }

    fn prepare(
        &self,
        admission: RuntimeParserAdmission<'_>,
    ) -> Result<Arc<dyn RuntimeParserBackend>, RuntimeError> {
        let grammar = admission.grammar();
        let admitted_grammar = admission.admitted_grammar();
        let image = admission.image();
        let limits = admission.limits();
        // Admission already ran the original executable verifier. The factory
        // additionally requires its own compiler/Unicode ABI, not merely an
        // arbitrary caller-supplied ABI accepted by that verifier.
        if image.compiler_abi != RUNTIME_COMPILER_ABI
            || image.unicode_version != RUNTIME_UNICODE_ABI
        {
            return Err(RuntimeError::Image("shared WPDA compiler/Unicode ABI mismatch".into()));
        }
        let receipt = grammar.wpda_original_occurrences.as_ref().ok_or_else(|| {
            RuntimeError::Image("original production occurrence receipt is unavailable".into())
        })?;
        let mut budget = PreparationBudget::new(limits);
        budget.occurrences(receipt.len())?;
        // Exact immutable producer order, including any occurrence multiplicity.
        // There is deliberately no authored-handle or classification filtering.
        let occurrences: Vec<_> = receipt.iter().map(|id| id.0 as usize).collect();
        let synthesis = derive_authored_rules_admitted(admitted_grammar, &occurrences, |event| {
            budget.event(event)
        })
        .map_err(preparation_error)?;
        let AuthoredSynthesisOutput {
            store,
            categories,
            per_category,
            source_order,
            policy: _,
        } = synthesis;
        let synthesis = AuthoredSynthesisOutput {
            store,
            categories,
            per_category,
            source_order,
            policy: (),
        };
        let descriptors = derive_authored_descriptors_admitted(
            admitted_grammar,
            &occurrences,
            synthesis,
            DescriptorOptions {
                crosscat_lex_compat_gate: true,
                prefix_factoring: false,
                mixfix_factoring: false,
                accept_continue: false,
                recovery_base: 0xFE00,
                max_mixfix_slice: usize::MAX,
            },
            |_, _, synthesis, _| budget.descriptors(synthesis),
            |_, _| {
                Err(RuntimeError::Image(
                    "cast source observation is unavailable in this descriptor profile".into(),
                ))
            },
        )
        .map_err(preparation_error)?;
        budget.actions_and_routing(&descriptors)?;
        let absorption = derive_absorption_rows_admitted(admitted_grammar, &descriptors)
            .map_err(preparation_error)?;
        let categories = authored_action_categories_admitted(admitted_grammar, &descriptors)
            .map_err(preparation_error)?;
        let primary = grammar
            .categories
            .iter()
            .find(|category| category.primary)
            .ok_or_else(|| RuntimeError::Image("primary category is unavailable".into()))?
            .id;
        let contextual_keywords = match &grammar.parser_configuration.reservation {
            KeywordReservation::None => Vec::new(),
            KeywordReservation::Auto { contextual } => {
                budget.contextual_keywords(contextual)?;
                contextual.iter().cloned().collect()
            },
        };
        Ok(Arc::new(PreparedBackend {
            descriptors,
            absorption,
            categories,
            primary,
            contextual_keywords,
            admission: limits,
        }))
    }
}

impl RuntimeParserBackend for PreparedBackend {
    fn parse(
        &self,
        session: &RuntimeLexicalSession<'_, '_, '_>,
        category: Option<CategoryId>,
        policy: RuntimePolicy,
    ) -> Result<Vec<WeightedParse>, RuntimeError> {
        let category = category.unwrap_or(self.primary);
        let primary = self
            .categories
            .iter()
            .position(|id| *id == category)
            .and_then(|index| u16::try_from(index).ok())
            .ok_or(RuntimeError::InvalidCategory(category))?;
        let source = OwnedTokenSource::from_admitted_session(
            session,
            SourceAdapterLimits {
                nodes: policy.max_lexer_states as usize,
                edges: policy.max_lexer_edges as usize,
                text_bytes: self.admission.max_encoded_bytes,
            },
        )
        .map_err(preparation_error)?;
        // All per-session action and routing metadata is admitted as a whole
        // before its existing constructors enter their classifier domains.
        let mut budget = PreparationBudget::new(self.admission);
        let actions = OwnedActionProvider::new(&source, &self.descriptors, |descriptors| {
            budget.actions_and_routing(descriptors).map_err(|error| {
                super::actions::OwnedActionBuildError::Source(format!("{error:?}"))
            })
        })
        .map_err(preparation_error)?;
        let engine = OwnedWpdaEngine::new(
            &self.descriptors,
            &actions,
            primary,
            &self.contextual_keywords,
            &self.absorption,
            |descriptors| {
                budget
                    .actions_and_routing(descriptors)
                    .map_err(|error| super::engine::OwnedEngineError::Source(format!("{error:?}")))
            },
        )
        .map_err(preparation_error)?;
        let mut walker = WpdaWalker::new_for_category_with_limits(
            engine,
            primary,
            0,
            WalkerResourceLimits {
                parse_items: policy.max_parse_items as usize,
                forest_nodes: policy.max_forest_nodes as usize,
            },
        )
        .with_semantic_key_cache_entries(policy.max_forest_nodes as usize)
        .with_semantic_key_logical_bytes(self.admission.max_encoded_bytes);
        walker
            .run_to_end_of_input_limited(&source)
            .map_err(resource_error)?;
        let roots = match walker.resolve_at_end_of_input(&source) {
            WpdaResolveResult::Accepted { roots, .. } => roots,
            WpdaResolveResult::RealizationFailed { error, .. } => {
                return Err(realization_error(error))
            },
            _ => return Err(RuntimeError::NoParse),
        };
        let cap = policy.max_semantic_results as usize;
        let mut output = Vec::new();
        for root in roots {
            let readings = walker
                .realize_root_complete_with_weights(root, cap)
                .map_err(realization_error)?;
            let size = output
                .len()
                .checked_add(readings.len())
                .ok_or(RuntimeError::SemanticResultLimit)?;
            if size > cap {
                return Err(RuntimeError::SemanticResultLimit);
            }
            output
                .try_reserve(readings.len())
                .map_err(|_| RuntimeError::SemanticResultLimit)?;
            for (value, weight) in readings {
                let term = value.downcast_ref::<OwnedTerm>().ok_or_else(|| {
                    RuntimeError::Reduction(
                        "original walker returned a non-owned category carrier".into(),
                    )
                })?;
                if term.category != primary {
                    return Err(RuntimeError::Reduction(
                        "original walker returned a different root category".into(),
                    ));
                }
                output.push(WeightedParse {
                    syntax: term.syntax.clone(),
                    value: term.value.clone(),
                    weight: ParseWeight::SharedWpda(weight),
                    production: term.production,
                });
            }
        }
        if output.is_empty() {
            Err(RuntimeError::NoParse)
        } else {
            Ok(output)
        }
    }
}

fn resource_error(error: WalkerResourceError) -> RuntimeError {
    match error {
        WalkerResourceError::ParseItemLimit { .. } => RuntimeError::ParseItemLimit,
        WalkerResourceError::ForestNodeLimit { .. } => RuntimeError::ForestNodeLimit,
        WalkerResourceError::LimitsNotInstalled => {
            RuntimeError::InvalidRuntimePolicy("original walker limits are not installed")
        },
    }
}

fn realization_error(error: RealizationError) -> RuntimeError {
    use mettail_semantic_key::ContentKeyCacheError as KeyError;
    match error {
        RealizationError::Resource(error) => resource_error(error),
        RealizationError::ResultOverflow { .. } => RuntimeError::SemanticResultLimit,
        RealizationError::SemanticKey(KeyError::ResourceExhausted { limit, requested }) => {
            RuntimeError::SemanticKeyEntryLimit { limit, requested }
        },
        RealizationError::SemanticKey(KeyError::KeyBytesExhausted { limit, requested }) => {
            RuntimeError::SemanticKeyByteLimit { limit, requested }
        },
        RealizationError::Action {
            cause: ActionInvocationError::RuntimeSemantic(error),
            ..
        } => error,
        other => RuntimeError::Reduction(format!("original WPDA realization: {other}")),
    }
}
