//! Action-table consumer for the admitted owned-engine domain.

use super::{decode_token, reduce, term_category, OwnedTerm};
use crate::wpda_owned::token_bindings::{matches_prefix, OwnedTokenBindings};
use crate::wpda_owned::{engine::OwnedEngineActions, source::OwnedTokenSource};
use crate::wpda_rule_analysis::{
    atomic_prefix::UnifiedDescriptor,
    authored_action::{
        authored_action_categories_admitted, derive_authored_action_shapes_admitted,
        AuthoredActionInput, AuthoredActionShape,
    },
    authored_descriptors::OwnedWpdaDescriptors,
    authored_synthesis::AuthoredRuleOrigin,
    prefix_bucket::PrefixBuckets,
    prefix_pattern::NeutralPattern,
};
use crate::wpda_runtime::{
    ActionArg, ActionContext, ActionInvocationError, ActionSignature, SemanticBuilder, ANY_CAT,
};
use mettail_grammar_core::{
    CategoryId, CollectionKind, DynamicValue, ProductionId, ReductionPlan, RuntimeError,
    SourceSpan, SyntaxItem, TokenId,
};
use std::any::Any;

#[derive(Debug)]
pub enum OwnedActionBuildError {
    Source(String),
    Unsupported {
        category: u16,
        rule: u16,
        feature: &'static str,
    },
    MissingCategory(String),
    InvalidProduction(usize),
    InvalidReduction(usize),
    Arity {
        category: u16,
        rule: u16,
        expected: usize,
        actual: usize,
    },
}

struct Row<'grammar> {
    plan: Option<&'grammar ReductionPlan>,
    expected: Vec<u16>,
    ignore_keyword: bool,
    decode_literal: bool,
    variable_category: Option<CategoryId>,
    literal_category: Option<CategoryId>,
    literal_token: Option<TokenId>,
    literal_home_patterns: Vec<(NeutralPattern, Option<NeutralPattern>)>,
    inputs: Vec<Input>,
    production: Option<ProductionId>,
    category_children: Vec<usize>,
}

enum Input {
    Term(u16),
    Collection { category: u16, kind: CollectionKind },
}

/// Retain only the original atomic home rows at this action's exact WPDA
/// coordinates. Core category IDs are a separate mapping, checked at decode.
fn literal_home_patterns(
    category: u16,
    rule: u16,
    buckets: &PrefixBuckets<NeutralPattern, NeutralPattern>,
) -> Vec<(NeutralPattern, Option<NeutralPattern>)> {
    buckets
        .1
        .iter()
        .filter_map(|key| buckets.0.get(key))
        .flat_map(|bucket| &bucket.descs)
        .filter_map(|descriptor| match descriptor {
            UnifiedDescriptor::Atomic(arm)
                if arm.category_src_idx == category && arm.rule_idx == rule =>
            {
                Some((arm.pattern.clone(), arm.extra_guard.clone()))
            },
            _ => None,
        })
        .collect()
}

/// Borrow the single collection slot already recognized by Core normalization.
/// The outer separator/nonempty semantics and reduction plan remain untouched;
/// this is not recursive wrapper normalization.
fn collection_action_slot(item: &SyntaxItem) -> Option<(&CategoryId, &CollectionKind)> {
    let source = match item {
        SyntaxItem::Separated { source, .. } => source.as_ref(),
        source => source,
    };
    match source {
        SyntaxItem::Collection { key: None, element, kind, .. } => Some((element, kind)),
        _ => None,
    }
}

pub struct OwnedActionProvider<'source, 'session, 'parser, 'input, 'grammar> {
    source: &'source OwnedTokenSource<'session, 'parser, 'input, 'grammar>,
    rows: Vec<Vec<Row<'grammar>>>,
    core_categories: Vec<CategoryId>,
    semantic_keys: Option<crate::wpda_owned::semantic_keys::OwnedSemanticKeys>,
}

impl<'source, 'session, 'parser, 'input, 'grammar>
    OwnedActionProvider<'source, 'session, 'parser, 'input, 'grammar>
{
    /// Admission prepays the complete classifier/action-row domain before
    /// source reads, classification, and allocation. No unsupported row is
    /// dropped. This callback is not a replacement for installed-grammar limits.
    pub fn new<P>(
        source: &'source OwnedTokenSource<'session, 'parser, 'input, 'grammar>,
        descriptors: &OwnedWpdaDescriptors<P>,
        admit: impl FnOnce(&OwnedWpdaDescriptors<P>) -> Result<(), OwnedActionBuildError>,
    ) -> Result<Self, OwnedActionBuildError> {
        admit(descriptors)?;
        if !crate::wpda_owned::structural::category_domain_is_disjoint(
            descriptors.synthesis.categories.len(),
        ) {
            return Err(OwnedActionBuildError::Source(
                "reserved structural category collision".into(),
            ));
        }
        let admitted = source.session().admitted_grammar();
        let grammar = admitted.grammar();
        let shapes = derive_authored_action_shapes_admitted(admitted, descriptors)
            .map_err(|error| OwnedActionBuildError::Source(format!("{error:?}")))?;
        let core_categories = authored_action_categories_admitted(admitted, descriptors)
            .map_err(|error| OwnedActionBuildError::Source(format!("{error:?}")))?;
        let mut rows = Vec::with_capacity(shapes.len());
        for (cat, shapes) in shapes.into_iter().enumerate() {
            let mut category_rows = Vec::with_capacity(shapes.len());
            for (rule, shape) in shapes.into_iter().enumerate() {
                let category = cat as u16;
                let local_rule = rule as u16;
                let unsupported = |feature| OwnedActionBuildError::Unsupported {
                    category,
                    rule: local_rule,
                    feature,
                };
                let origin = descriptors.synthesis.per_category[cat][rule].origin;
                if origin == AuthoredRuleOrigin::Synthetic
                    && matches!(shape, AuthoredActionShape::Variable)
                {
                    let core_category = core_categories[cat];
                    if !grammar
                        .categories
                        .get(core_category.0 as usize)
                        .is_some_and(|category| category.admits_variables)
                    {
                        return Err(unsupported("declared category forbids variables"));
                    }
                    category_rows.push(Row {
                        plan: None,
                        expected: vec![ANY_CAT],
                        ignore_keyword: false,
                        decode_literal: false,
                        variable_category: Some(core_category),
                        literal_category: None,
                        literal_token: None,
                        literal_home_patterns: Vec::new(),
                        inputs: Vec::new(),
                        production: None,
                        category_children: Vec::new(),
                    });
                    continue;
                }
                if origin == AuthoredRuleOrigin::Synthetic
                    && matches!(shape, AuthoredActionShape::Literal)
                {
                    category_rows.push(Row {
                        plan: None,
                        expected: vec![ANY_CAT],
                        ignore_keyword: false,
                        decode_literal: true,
                        variable_category: None,
                        literal_category: Some(core_categories[cat]),
                        literal_token: None,
                        literal_home_patterns: literal_home_patterns(
                            category,
                            local_rule,
                            &descriptors.prefixes[cat],
                        ),
                        inputs: Vec::new(),
                        production: None,
                        category_children: Vec::new(),
                    });
                    continue;
                }
                let AuthoredRuleOrigin::User { production_index, .. } = origin else {
                    return Err(unsupported("synthetic semantic binding"));
                };
                let production = grammar
                    .productions
                    .get(production_index)
                    .ok_or(OwnedActionBuildError::InvalidProduction(production_index))?;
                let plan = grammar
                    .reductions
                    .get(production.reduction as usize)
                    .ok_or(OwnedActionBuildError::InvalidReduction(
                        production.reduction as usize,
                    ))?;
                let decode_literal = matches!(shape, AuthoredActionShape::Literal);
                let mut inputs = Vec::new();
                let mut literal_token = None;
                let lookup = |name: String| {
                    descriptors
                        .synthesis
                        .categories
                        .iter()
                        .position(|category| category == &name)
                        .map(|index| index as u16)
                        .ok_or(OwnedActionBuildError::MissingCategory(name))
                };
                let (expected, ignore_keyword) = match shape {
                    AuthoredActionShape::Variable => {
                        return Err(unsupported("nonsynthetic variable action"))
                    },
                    AuthoredActionShape::Literal => {
                        let [SyntaxItem::CaptureToken { token, .. }] = production.syntax.as_slice()
                        else {
                            return Err(unsupported("authored literal token binding"));
                        };
                        literal_token = Some(*token);
                        (vec![ANY_CAT], false)
                    },
                    AuthoredActionShape::Inputs(shapes) => {
                        let mut expected = Vec::with_capacity(shapes.len());
                        for (index, shape) in shapes.into_iter().enumerate() {
                            match shape {
                                AuthoredActionInput::Term(name) => {
                                    let category = lookup(name)?;
                                    expected.push(category);
                                    inputs.push(Input::Term(category));
                                },
                                AuthoredActionInput::Collection { category: name, kind } => {
                                    if matches!(kind, CollectionKind::Map | CollectionKind::PathMap)
                                    {
                                        return Err(unsupported("key/value collection action"));
                                    }
                                    let category = lookup(name)?;
                                    let Some((element, actual_kind)) = production
                                        .syntax
                                        .iter()
                                        .filter(|item| !matches!(item, SyntaxItem::Token(_)))
                                        .nth(index)
                                        .and_then(collection_action_slot)
                                    else {
                                        return Err(unsupported(
                                            "collection requires exact authored slot",
                                        ));
                                    };
                                    if *element != core_categories[usize::from(category)]
                                        || *actual_kind != kind
                                    {
                                        return Err(unsupported(
                                            "collection slot differs from original action",
                                        ));
                                    }
                                    expected.push(ANY_CAT);
                                    inputs.push(Input::Collection { category, kind });
                                },
                            }
                        }
                        (expected, false)
                    },
                    AuthoredActionShape::Keyword => (vec![ANY_CAT], true),
                    AuthoredActionShape::Unsupported(feature) => return Err(unsupported(feature)),
                };
                let actual = if ignore_keyword { 0 } else { expected.len() };
                if actual != usize::from(plan.input_arity) || expected.len() > usize::from(u8::MAX)
                {
                    return Err(OwnedActionBuildError::Arity {
                        category,
                        rule: local_rule,
                        expected: usize::from(plan.input_arity),
                        actual,
                    });
                }
                // Ranked rows use only the checked flat category-slot bridge.
                // Unranked rows retain the original worker's early return.
                let mut category_children = Vec::new();
                if production.precedence.binding_power.is_some() {
                    let mut index = 0;
                    for item in &production.syntax {
                        match item {
                            SyntaxItem::Token(_) => {},
                            SyntaxItem::Category { category: actual_category, .. } => {
                                let Some(Input::Term(category)) = inputs.get(index) else {
                                    return Err(unsupported(
                                        "ranked source/action category bridge",
                                    ));
                                };
                                if *actual_category != core_categories[usize::from(*category)] {
                                    return Err(unsupported(
                                        "ranked source/action category mismatch",
                                    ));
                                }
                                if *actual_category == production.result {
                                    category_children.push(index);
                                }
                                index += 1;
                            },
                            _ => return Err(unsupported("ranked nonflat action")),
                        }
                    }
                    if index != inputs.len() {
                        return Err(unsupported("ranked source/action arity bridge"));
                    }
                }
                category_rows.push(Row {
                    plan: Some(plan),
                    expected,
                    ignore_keyword,
                    decode_literal,
                    variable_category: None,
                    literal_category: None,
                    literal_token,
                    literal_home_patterns: Vec::new(),
                    inputs,
                    production: Some(production.id),
                    category_children,
                });
            }
            rows.push(category_rows);
        }
        let semantic_keys =
            crate::wpda_owned::semantic_keys::OwnedSemanticKeys::new(source, descriptors);
        Ok(Self {
            source,
            rows,
            core_categories,
            semantic_keys,
        })
    }

    fn row(&self, category: u16, rule: u16) -> Option<&Row<'grammar>> {
        self.rows.get(usize::from(category))?.get(usize::from(rule))
    }

    fn span(&self, context: ActionContext) -> Result<SourceSpan, ActionInvocationError> {
        let (lo, hi) = context
            .source_positions
            .ok_or(ActionInvocationError::MissingActionContext)?;
        let start = self
            .source
            .position(lo as usize)
            .ok_or(ActionInvocationError::InvalidActionContext)?
            .offset;
        let end = self
            .source
            .position(hi as usize)
            .ok_or(ActionInvocationError::InvalidActionContext)?
            .offset;
        // Exact apply_rule projection: the logical EOF edge may end one past
        // input.end. Structural holes already have their original logical width.
        let end = end.min(self.source.session().input_end());
        if start > end {
            return Err(ActionInvocationError::InvalidActionContext);
        }
        Ok(SourceSpan {
            start: u32::try_from(start).map_err(|_| ActionInvocationError::InvalidActionContext)?,
            end: u32::try_from(end).map_err(|_| ActionInvocationError::InvalidActionContext)?,
        })
    }

    fn literal(
        &self,
        category: u16,
        arg: &ActionArg,
        span: SourceSpan,
        expected_category: Option<CategoryId>,
        expected_token: Option<TokenId>,
        home_patterns: &[(NeutralPattern, Option<NeutralPattern>)],
    ) -> Result<Option<OwnedTerm>, ActionInvocationError> {
        let ActionArg::Token { kind, text, pos, occurrence } = arg else {
            return Ok(None);
        };
        let occurrence = occurrence.ok_or(ActionInvocationError::MissingTokenOccurrence)?;
        let edge = self
            .source
            .token_occurrence(*pos, occurrence as usize)
            .ok_or(ActionInvocationError::InvalidTokenOccurrence)?;
        let start = self
            .source
            .position(*pos)
            .ok_or(ActionInvocationError::InvalidTokenOccurrence)?;
        let definition = self
            .source
            .session()
            .grammar()
            .tokens
            .get(edge.token.0 as usize)
            .ok_or(ActionInvocationError::InvalidTokenOccurrence)?;
        if expected_token.is_some_and(|token| token != edge.token) {
            return Err(ActionInvocationError::InvalidTokenOccurrence);
        }
        if self
            .source
            .session()
            .input_slice(start.offset, edge.end.offset)
            != Some(text.as_str())
        {
            return Err(ActionInvocationError::InvalidTokenOccurrence);
        }
        if let Some(category) = expected_category {
            // Synthetic native literals use the original retained token-kind
            // observation, never a decoder inferred from spelling. Macro Core
            // builtins may lack a category tag; only the original home literal
            // pattern/guard can authorize that absence. A contradictory tag is
            // still refused. Authored exact-token captures keep their old path.
            let actual_kind = OwnedTokenBindings::new(self.source.session().grammar())
                .and_then(|bindings| bindings.resolve(edge.token, text))
                .map_err(|_| ActionInvocationError::InvalidTokenOccurrence)?;
            let category_matches = match definition.category {
                Some(actual) => actual == category,
                None => home_patterns
                    .iter()
                    .any(|(pattern, guard)| matches_prefix(pattern, guard.as_ref(), kind)),
            };
            if actual_kind != *kind || !category_matches {
                return Err(ActionInvocationError::InvalidTokenOccurrence);
            }
        }
        decode_token(self.source.session(), category, edge.token, text, span).map(Some)
    }

    fn collection(
        category: u16,
        kind: CollectionKind,
        drained: Vec<ActionArg>,
        span: SourceSpan,
    ) -> Result<Option<OwnedTerm>, ActionInvocationError> {
        let items = match ActionArg::try_into_terms::<OwnedTerm>(drained) {
            Ok(items) => items,
            Err(_) => {
                crate::wpda_runtime::note_coll_action_downcast_abandon();
                return Ok(None);
            },
        };
        if items.iter().any(|item| item.category != category) {
            crate::wpda_runtime::note_coll_action_downcast_abandon();
            return Ok(None);
        }
        // Exact FinalizeCollection projection order: syntax, then values.
        let syntax =
            DynamicValue::collection(kind, items.iter().map(|item| item.syntax.clone()).collect())
                .map_err(Self::collection_error)?;
        let value =
            DynamicValue::collection(kind, items.iter().map(|item| item.value.clone()).collect())
                .map_err(Self::collection_error)?;
        Ok(Some(OwnedTerm {
            category: ANY_CAT,
            production: None,
            syntax,
            value,
            span,
        }))
    }

    fn collection_error(
        error: mettail_grammar_core::DynamicCollectionError,
    ) -> ActionInvocationError {
        ActionInvocationError::RuntimeSemantic(RuntimeError::from(error))
    }
}

impl OwnedEngineActions for OwnedActionProvider<'_, '_, '_, '_, '_> {
    fn supports_structural_holes(&self) -> bool {
        true
    }
    fn structural_hole_edge(&self, category: u16, pos: usize) -> Option<(usize, u32)> {
        let core_category = *self.core_categories.get(usize::from(category))?;
        let edge = self.source.structural_hole_edge(core_category, pos)?;
        let end = self
            .source
            .node_id(edge.end)
            .expect("source admission checked every structural endpoint");
        Some((end, crate::wpda_owned::structural::HOLE_ACTION))
    }
    fn grouping_boundary_rule(&self) -> Option<u32> {
        Some(crate::wpda_owned::structural::GROUPING_ACTION)
    }
    fn action_signature(&self, category: u16, rule: u16) -> Option<ActionSignature<'_>> {
        if (category, rule)
            == (
                crate::wpda_owned::structural::CATEGORY,
                crate::wpda_owned::structural::GROUPING_RULE,
            )
        {
            return Some(ActionSignature {
                arity: 1,
                expected_input_cats: &[ANY_CAT],
                output_cat: ANY_CAT,
            });
        }
        if (category, rule)
            == (
                crate::wpda_owned::structural::CATEGORY,
                crate::wpda_owned::structural::HOLE_RULE,
            )
        {
            return Some(ActionSignature {
                arity: 0,
                expected_input_cats: &[],
                output_cat: ANY_CAT,
            });
        }
        let row = self.row(category, rule)?;
        Some(ActionSignature {
            arity: row.expected.len() as u8,
            expected_input_cats: &row.expected,
            output_cat: category,
        })
    }

    fn execute_action(
        &self,
        _: u16,
        _: u16,
        _: &mut SemanticBuilder,
        _: Vec<ActionArg>,
    ) -> Result<(), ActionInvocationError> {
        Err(ActionInvocationError::MissingActionContext)
    }

    fn execute_action_with_context(
        &self,
        category: u16,
        rule: u16,
        builder: &mut SemanticBuilder,
        args: Vec<ActionArg>,
        context: ActionContext,
    ) -> Result<(), ActionInvocationError> {
        if (category, rule)
            == (
                crate::wpda_owned::structural::CATEGORY,
                crate::wpda_owned::structural::GROUPING_RULE,
            )
        {
            return super::grouping_boundary(builder, args);
        }
        if (category, rule)
            == (
                crate::wpda_owned::structural::CATEGORY,
                crate::wpda_owned::structural::HOLE_RULE,
            )
        {
            if !args.is_empty() {
                return Err(ActionInvocationError::Arity { expected: 0, actual: args.len() });
            }
            let category = context
                .result_category
                .ok_or(ActionInvocationError::MissingActionContext)?;
            let core_category = *self
                .core_categories
                .get(usize::from(category))
                .ok_or(ActionInvocationError::InvalidActionContext)?;
            let (lo, hi) = context
                .source_positions
                .ok_or(ActionInvocationError::MissingActionContext)?;
            let edge = self
                .source
                .structural_hole_edge(core_category, lo as usize)
                .ok_or(ActionInvocationError::InvalidActionContext)?;
            if self.source.position(lo as usize) != Some(edge.start)
                || self.source.position(hi as usize) != Some(edge.end)
            {
                return Err(ActionInvocationError::InvalidActionContext);
            }
            let span = self.span(context)?;
            builder.push_term(super::structural_hole(category, edge.id, edge.category, span));
            return Ok(());
        }
        let span = self.span(context)?;
        let row = self
            .row(category, rule)
            .ok_or(ActionInvocationError::MissingAction { category, rule })?;
        if args.len() != row.expected.len() {
            return Err(ActionInvocationError::Arity {
                expected: row.expected.len(),
                actual: args.len(),
            });
        }
        let mut inputs = Vec::new();
        if let Some(core_category) = row.variable_category {
            builder.push_term(super::native_variable(category, core_category, args, span));
            return Ok(());
        }
        if row.decode_literal {
            let Some(term) = self.literal(
                category,
                &args[0],
                span,
                row.literal_category,
                row.literal_token,
                &row.literal_home_patterns,
            )?
            else {
                return Ok(());
            };
            if row.plan.is_none() {
                // Original runtime TokenValue preserves the decoded scalar in
                // both projections; no constructor or synthetic plan is made.
                builder.push_term(term);
                return Ok(());
            }
            inputs.push(term);
        } else if !row.ignore_keyword {
            let mut values = vec![None; row.inputs.len()];
            let mut collections = Vec::new();
            // Original phase 1: source-order argument and ID extraction.
            for (index, (arg, input)) in args.iter().zip(&row.inputs).enumerate() {
                match input {
                    Input::Term(expected) => {
                        let ActionArg::Term { value, .. } = arg else {
                            return Ok(());
                        };
                        let Some(term) = value.downcast_ref::<OwnedTerm>() else {
                            return Ok(());
                        };
                        if term.category != *expected {
                            return Ok(());
                        }
                        values[index] = Some(term.clone());
                    },
                    Input::Collection { category, kind } => {
                        let Some(id) = arg.as_collection_id() else {
                            return Ok(());
                        };
                        collections.push((index, id, *category, *kind));
                    },
                }
            }
            // Original reverse-site loop: drain and immediately materialize.
            for (index, id, category, kind) in collections.into_iter().rev() {
                let drained = builder.drain_collection(id);
                let Some(value) = Self::collection(category, kind, drained, span)? else {
                    return Ok(());
                };
                values[index] = Some(value);
            }
            inputs = values
                .into_iter()
                .map(|value| value.expect("every admitted action slot was materialized"))
                .collect();
        }
        let tops = inputs
            .iter()
            .map(|input| input.production)
            .collect::<Vec<_>>();
        if !mettail_grammar_core::production_precedence_valid(
            self.source.session().grammar(),
            row.production,
            &tops,
            |_| row.category_children.clone(),
        ) {
            return Ok(());
        }
        let plan = row
            .plan
            .expect("admitted non-TokenValue rows retain their exact production plan");
        let mut term = reduce(self.source.session(), category, plan, &inputs, &[], span)?;
        term.production = row.production;
        builder.push_term(term);
        Ok(())
    }

    fn term_category(&self, value: &(dyn Any + Send + Sync)) -> Option<u16> {
        term_category(value)
    }

    fn semantic_content_key(
        &self,
        term: &std::sync::Arc<dyn Any + Send + Sync>,
        cache: &mut mettail_semantic_key::ContentKeyCache,
    ) -> Result<Option<mettail_semantic_key::ContentKey>, mettail_semantic_key::ContentKeyCacheError>
    {
        match &self.semantic_keys {
            Some(keys) => keys.content_key(term, cache),
            None => Ok(None),
        }
    }
}

#[cfg(test)]
mod tests;
