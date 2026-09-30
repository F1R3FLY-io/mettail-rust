//! Owned routing through the original shared WPDA transition bodies.
//!
//! Admission is deliberately explicit. Unsupported source rows fail before an
//! engine is published; they never disappear from a live dispatch. This initial
//! routing domain is not the complete installed-grammar/Regex domain.

use crate::automata::{lex_weight::LexicographicWeight, TokenKind};
use crate::binding_power::IterAbsorbSpec;
use crate::gss::{WpdaGss, WpdaGssNode};
use crate::wpda_rule_analysis::atomic_prefix::UnifiedDescriptor;
use crate::wpda_rule_analysis::authored::AuthoredRuleReader;
use crate::wpda_rule_analysis::authored_binder::derive_authored_binder;
use crate::wpda_rule_analysis::authored_descriptors::OwnedWpdaDescriptors;
use crate::wpda_rule_analysis::binder::optional::{BinderSyntaxObservation, BinderSyntaxReader};
use crate::wpda_rule_analysis::binder::rule::BinderRuleReader;
use crate::wpda_rule_analysis::binder::term_param::{TermParamObservation, TermParamReader};
use crate::wpda_rule_analysis::binder::{
    binder_initial_body_cat, required_top_cat_after_position, BinderPosition, BinderShape,
};
use crate::wpda_rule_analysis::collection::assembly::has_binder_internal_collection_slot;
use crate::wpda_rule_analysis::fork_emission::ForkEmissionOrdinalModel;
use crate::wpda_rule_analysis::mixfix::group_ops_by_cat_terminal;
use crate::wpda_rule_analysis::prefix_bucket::HolePrefixKind;
use crate::wpda_rule_analysis::rule_observation;
use crate::wpda_runtime::{
    lex_one as one, lex_w as cost, lex_w_alt, lex_w_alt_with_len, lex_w_with_len,
};
use crate::wpda_runtime::{
    ActionArg, ActionInvocationError, ActionSignature, FrameCtx, LexAltRuleInfo, LexAltRuleKind,
    SemanticBuilder, StackSymbolV2, SymbolKind, WpdaState, WpdaTokenSource,
};
use crate::wpda_transitions::{
    binder, collection_loop, control, infix, lexical_fork, mixfix, prefix, prefix_dispatch,
    unwinding,
};
use crate::wpda_walker::{ForkActionKind, TriggerMode, WpdaEngine, WpdaStepAction};
use std::any::Any;
use std::collections::BTreeMap;

/// Contextual action execution is supplied by the installed semantic adapter.
/// There is no missing-action or guessed-category default.
pub trait OwnedEngineActions {
    fn supports_structural_holes(&self) -> bool {
        false
    }
    fn structural_hole_edge(&self, _category: u16, _pos: usize) -> Option<(usize, u32)> {
        None
    }
    fn grouping_boundary_rule(&self) -> Option<u32> {
        None
    }
    fn action_signature(&self, category: u16, rule: u16) -> Option<ActionSignature<'_>>;
    fn execute_action(
        &self,
        category: u16,
        rule: u16,
        builder: &mut SemanticBuilder,
        args: Vec<ActionArg>,
    ) -> Result<(), ActionInvocationError>;
    fn execute_action_with_context(
        &self,
        category: u16,
        rule: u16,
        builder: &mut SemanticBuilder,
        args: Vec<ActionArg>,
        _context: crate::wpda_runtime::ActionContext,
    ) -> Result<(), ActionInvocationError> {
        self.execute_action(category, rule, builder, args)
    }
    fn term_category(&self, value: &(dyn Any + Send + Sync)) -> Option<u16>;

    /// Exact parser-local key, or explicit unavailable-profile observation.
    /// Infallible legacy fingerprint hooks remain conservative defaults: a
    /// checked projection/cache failure must travel through this Result hook.
    fn semantic_content_key(
        &self,
        _term: &std::sync::Arc<dyn Any + Send + Sync>,
        _cache: &mut mettail_semantic_key::ContentKeyCache,
    ) -> Result<Option<mettail_semantic_key::ContentKey>, mettail_semantic_key::ContentKeyCacheError>
    {
        Ok(None)
    }
}

/// Existing absorption query results must be supplied, including explicit None.
/// A missing query row is not interpreted as permission to disable absorption.
pub type AbsorptionRows = BTreeMap<(u16, u16, u16), Option<IterAbsorbSpec>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OwnedEngineError {
    MissingCategory(u16),
    MissingAction {
        category: u16,
        rule: u16,
    },
    MissingAbsorption {
        category: u16,
        result: u16,
        rule: u16,
    },
    Unsupported {
        category: u16,
        rule: u16,
        feature: &'static str,
    },
    Source(String),
}

struct Rule<'grammar> {
    binder: Option<BinderShape>,
    trigger: Option<&'grammar str>,
    nullary: Option<Vec<&'grammar str>>,
    leading_literal: bool,
    min_terminal_span: u32,
    represented: bool,
}

#[derive(Default)]
struct OperatorRows {
    infix: Vec<(u8, u8, u16, u16)>,
    postfix: Vec<(u8, u16, u16)>,
    mixfix: Vec<(u8, u16, u16)>,
    lexical: Vec<LexAltRuleInfo>,
}

struct Part<'grammar> {
    operand: u16,
    preceding: Vec<&'grammar str>,
    following: Vec<&'grammar str>,
    capture: Option<&'grammar str>,
}

pub struct OwnedWpdaEngine<'grammar, P> {
    descriptors: &'grammar OwnedWpdaDescriptors<P>,
    actions: &'grammar dyn OwnedEngineActions,
    primary: u16,
    contextual_keywords: &'grammar [String],
    absorption: &'grammar AbsorptionRows,
    rules: Vec<Vec<Rule<'grammar>>>,
    operators: Vec<BTreeMap<String, OperatorRows>>,
    parts: BTreeMap<(u16, u16), Vec<Part<'grammar>>>,
    fork_ordinals: ForkEmissionOrdinalModel,
}

impl<'grammar, P> OwnedWpdaEngine<'grammar, P> {
    /// Borrow a previously admitted descriptor artifact and its complete action
    /// and absorption observations. `admit` prepays this finite routing assembly.
    /// No fallback parser or repair engine is installed by this constructor.
    pub fn new(
        descriptors: &'grammar OwnedWpdaDescriptors<P>,
        actions: &'grammar dyn OwnedEngineActions,
        primary: u16,
        contextual_keywords: &'grammar [String],
        absorption: &'grammar AbsorptionRows,
        admit: impl FnOnce(&OwnedWpdaDescriptors<P>) -> Result<(), OwnedEngineError>,
    ) -> Result<Self, OwnedEngineError> {
        admit(descriptors)?;
        let categories = &descriptors.synthesis.categories;
        if !crate::wpda_owned::structural::category_domain_is_disjoint(categories.len()) {
            return Err(OwnedEngineError::Source("reserved structural category collision".into()));
        }
        if usize::from(primary) >= categories.len() {
            return Err(OwnedEngineError::MissingCategory(primary));
        }
        let unsupported =
            |category, rule, feature| OwnedEngineError::Unsupported { category, rule, feature };
        if descriptors
            .factoring_emission
            .dispositions
            .iter()
            .any(|rows| !rows.is_empty())
            || !descriptors.factoring_emission.mixfix_groups.is_empty()
        {
            return Err(unsupported(primary, 0, "factored spine routing"));
        }
        if descriptors
            .collections
            .iter()
            .any(|row| !row.spec.close_resumes_via_unwinding)
        {
            return Err(unsupported(primary, 0, "standalone collection prefix routing"));
        }
        let reader = AuthoredRuleReader::new(&descriptors.synthesis.store)
            .map_err(|error| OwnedEngineError::Source(error.to_string()))?;
        let mut rules = Vec::with_capacity(categories.len());
        for (category, source_rules) in descriptors.synthesis.per_category.iter().enumerate() {
            let category = u16::try_from(category).expect("descriptor category admission");
            let mut rows = Vec::with_capacity(source_rules.len());
            for (rule, payload) in source_rules.iter().enumerate() {
                let rule = u16::try_from(rule).expect("descriptor rule admission");
                if actions.action_signature(category, rule).is_none() {
                    return Err(OwnedEngineError::MissingAction { category, rule });
                }
                if let Some(params) = reader.term_context(payload.rule) {
                    for index in 0..reader.params_len(params) {
                        if !matches!(
                            reader.param(
                                reader
                                    .param_at(params, index)
                                    .expect("parameter index is in bounds")
                            ),
                            TermParamObservation::Simple { .. }
                        ) {
                            return Err(unsupported(
                                category,
                                rule,
                                "scope/guard/optional action metadata",
                            ));
                        }
                    }
                }
                let shape = derive_authored_binder(&reader, payload.rule, |_, _, _| {
                    Ok::<_, std::convert::Infallible>(())
                })
                .map_err(|error| OwnedEngineError::Source(format!("{error:?}")))?;
                if let Some(shape) = &shape {
                    if shape.has_binder || shape.is_multi {
                        return Err(unsupported(category, rule, "binder scope/list routing"));
                    }
                    for position in &shape.positions {
                        match position {
                            BinderPosition::Literal(_)
                            | BinderPosition::IdentTextCapture { .. }
                            | BinderPosition::TokenKindCapture { .. } => {},
                            BinderPosition::ParamParse { cat, collection } => {
                                if !categories.contains(cat) {
                                    return Err(OwnedEngineError::Source(format!(
                                        "unknown operand category {cat}"
                                    )));
                                }
                                if let Some(info) = collection {
                                    if !descriptors
                                        .collections
                                        .iter()
                                        .any(|row| row.key == (category, rule, info.slot_idx))
                                    {
                                        return Err(unsupported(
                                            category,
                                            rule,
                                            "missing original collection slot descriptor",
                                        ));
                                    }
                                }
                            },
                            _ => {
                                return Err(unsupported(
                                    category,
                                    rule,
                                    "nested binder/collection/guest position",
                                ))
                            },
                        }
                    }
                }
                let trigger = rule_observation::leading_literal(&reader, payload.rule);
                let min_terminal_span = rule_observation::min_terminal_span(&reader, payload.rule);
                rows.push(Rule {
                    binder: shape,
                    trigger,
                    nullary: None,
                    leading_literal: trigger.is_some(),
                    min_terminal_span,
                    represented: false,
                });
            }
            rules.push(rows);
        }
        let mut fork_ordinals = ForkEmissionOrdinalModel::new();
        for category in 0..rules.len() {
            let category = u16::try_from(category).expect("descriptor category admission");
            let local_paren = rules[usize::from(category)]
                .iter()
                .any(|row| row.binder.is_some() && row.trigger == Some("("));
            let sources = if local_paren {
                vec![category]
            } else {
                descriptors.grouping_sources[usize::from(category)].clone()
            };
            let mut paren_position =
                u16::try_from(sources.len()).expect("descriptor grouping admission");
            for owner in sources {
                for (rule, row) in rules[usize::from(owner)].iter_mut().enumerate() {
                    if row.binder.is_some() && row.trigger == Some("(") {
                        row.represented = true;
                        fork_ordinals.record_site2_row(
                            owner,
                            u16::try_from(rule).expect("descriptor rule admission"),
                            paren_position,
                            "paren-dispatch \"(\"",
                        );
                        paren_position += 1;
                    }
                }
            }
        }
        // The original bucket descriptor discriminants determine routes. No
        // source syntax is reclassified into a second transition language.
        for (category, (buckets, order)) in descriptors.prefixes.iter().enumerate() {
            let category = u16::try_from(category).expect("descriptor category admission");
            for key in order {
                for (position, desc) in buckets[key].descs.iter().enumerate() {
                    let rule_idx = match desc {
                        UnifiedDescriptor::Atomic(arm) => Some(arm.rule_idx),
                        UnifiedDescriptor::BinderPrefix { rule_idx, .. }
                        | UnifiedDescriptor::LeadingCategory { rule_idx, .. }
                        | UnifiedDescriptor::CrossCatProjection { rule_idx, .. }
                        | UnifiedDescriptor::NullaryLiteralRun { rule_idx } => Some(*rule_idx),
                        _ => None,
                    };
                    if let Some(rule_idx) = rule_idx {
                        rules[usize::from(category)][usize::from(rule_idx)].represented = true;
                        fork_ordinals.record_site2_row(
                            category,
                            rule_idx,
                            u16::try_from(position).expect("descriptor bucket admission"),
                            &format!("prefix-dispatch {key:?}"),
                        );
                    }
                    match desc {
                        UnifiedDescriptor::Atomic(_) | UnifiedDescriptor::BinderPrefix { .. } => {},
                        UnifiedDescriptor::LeadingCategory { rule_idx, source_src_idx } => {
                            if *source_src_idx != category {
                                return Err(unsupported(
                                    category,
                                    *rule_idx,
                                    "cross-category leading operand metadata",
                                ));
                            }
                        },
                        UnifiedDescriptor::NullaryLiteralRun { rule_idx } => {
                            let payload = descriptors.synthesis.per_category[usize::from(category)]
                                [usize::from(*rule_idx)];
                            let syntax = reader
                                .syntax_pattern(payload.rule)
                                .expect("nullary descriptor syntax");
                            let mut tail = Vec::new();
                            for index in 1..reader.sequence_len(syntax) {
                                let Some(BinderSyntaxObservation::Literal(text)) =
                                    reader.at(syntax, index)
                                else {
                                    return Err(unsupported(
                                        category,
                                        *rule_idx,
                                        "inconsistent nullary descriptor",
                                    ));
                                };
                                tail.push(text);
                            }
                            rules[usize::from(category)][usize::from(*rule_idx)].nullary =
                                Some(tail);
                        },
                        UnifiedDescriptor::CrossCatLhs { .. } => {
                            return Err(unsupported(
                                category,
                                0,
                                "cross-category LHS policy metadata",
                            ))
                        },
                        UnifiedDescriptor::CrossCatProjection { .. } => {},
                        UnifiedDescriptor::CrossCatPrefixUnary { rule_idx, .. } => {
                            return Err(unsupported(
                                category,
                                *rule_idx,
                                "cross-category realization metadata",
                            ))
                        },
                        UnifiedDescriptor::LeadingTokenKindCapture { rule_idx, .. }
                        | UnifiedDescriptor::LeadingGuestBody { rule_idx, .. } => {
                            return Err(unsupported(
                                category,
                                *rule_idx,
                                "borrowed lexical capture metadata",
                            ))
                        },
                    }
                }
            }
        }
        let grouped = group_ops_by_cat_terminal(
            &descriptors.binding_powers,
            categories,
            &descriptors.label_index,
        );
        let mut operators: Vec<BTreeMap<String, OperatorRows>> =
            (0..categories.len()).map(|_| BTreeMap::new()).collect();
        let mut parts = BTreeMap::new();
        for ((category, terminal), group) in grouped {
            let mut row = OperatorRows::default();
            for g in &group {
                let op = g.op;
                rules[usize::from(g.result_src_idx)][usize::from(g.rule_idx)].represented = true;
                if op.is_cross_category {
                    return Err(unsupported(
                        category,
                        g.rule_idx,
                        "cross-category operator policy metadata",
                    ));
                }
                if op.is_iterative_candidate()
                    && !absorption.contains_key(&(category, g.result_src_idx, g.rule_idx))
                {
                    return Err(OwnedEngineError::MissingAbsorption {
                        category,
                        result: g.result_src_idx,
                        rule: g.rule_idx,
                    });
                }
                if op.is_mixfix {
                    let mut part_rows = Vec::new();
                    for part in &op.mixfix_parts {
                        if part.repetition.is_some() {
                            return Err(unsupported(
                                category,
                                g.rule_idx,
                                "mixfix repetition routing",
                            ));
                        }
                        let operand = if part.capture_kind.is_some() {
                            u16::MAX
                        } else {
                            categories
                                .iter()
                                .position(|name| name == &part.operand_category)
                                .and_then(|index| u16::try_from(index).ok())
                                .ok_or_else(|| {
                                    OwnedEngineError::Source(format!(
                                        "unknown mixfix operand {}",
                                        part.operand_category
                                    ))
                                })?
                        };
                        part_rows.push(Part {
                            operand,
                            preceding: part
                                .preceding_terminals
                                .iter()
                                .map(String::as_str)
                                .collect(),
                            following: part
                                .following_terminals
                                .iter()
                                .map(String::as_str)
                                .collect(),
                            capture: part.capture_kind.as_deref(),
                        });
                    }
                    parts.insert((g.result_src_idx, g.rule_idx), part_rows);
                    if !op.nullary_literals.is_empty() {
                        rules[usize::from(g.result_src_idx)][usize::from(g.rule_idx)].nullary =
                            Some(op.nullary_literals.iter().map(String::as_str).collect());
                    }
                }
            }
            // These are the original three per-tier filters and independent caps.
            row.infix.extend(
                group
                    .iter()
                    .filter(|g| !g.op.is_postfix && !g.op.is_mixfix)
                    .take(descriptors.options.max_mixfix_slice)
                    .map(|g| (g.op.left_bp, g.op.right_bp, g.result_src_idx, g.rule_idx)),
            );
            row.postfix.extend(
                group
                    .iter()
                    .filter(|g| g.op.is_postfix)
                    .take(descriptors.options.max_mixfix_slice)
                    .map(|g| (g.op.left_bp, g.result_src_idx, g.rule_idx)),
            );
            row.mixfix.extend(
                group
                    .iter()
                    .filter(|g| g.op.is_mixfix)
                    .take(descriptors.options.max_mixfix_slice)
                    .map(|g| (g.op.left_bp, g.result_src_idx, g.rule_idx)),
            );
            // The original lexical table does not apply the Pratt slice cap.
            for g in &group {
                let op = g.op;
                let kind = if op.is_postfix {
                    LexAltRuleKind::PostfixOp {
                        l_bp: op.left_bp,
                        result_src_idx: g.result_src_idx,
                    }
                } else if op.is_mixfix {
                    LexAltRuleKind::MixfixFirstTrigger {
                        l_bp: op.left_bp,
                        result_src_idx: g.result_src_idx,
                    }
                } else {
                    LexAltRuleKind::InfixOp {
                        l_bp: op.left_bp,
                        r_bp: op.right_bp,
                        result_src_idx: g.result_src_idx,
                    }
                };
                row.lexical
                    .push(LexAltRuleInfo { rule_idx: g.rule_idx, kind });
            }
            operators[usize::from(category)].insert(terminal, row);
        }
        for (category, rows) in rules.iter().enumerate() {
            for (rule, row) in rows.iter().enumerate() {
                if !row.represented {
                    return Err(unsupported(
                        u16::try_from(category).expect("descriptor category admission"),
                        u16::try_from(rule).expect("descriptor rule admission"),
                        "rule has no admitted original dispatch row",
                    ));
                }
            }
        }
        Ok(Self {
            descriptors,
            actions,
            primary,
            contextual_keywords,
            absorption,
            rules,
            operators,
            parts,
            fork_ordinals,
        })
    }

    fn row(&self, category: u16, rule: u16) -> Option<&Rule<'grammar>> {
        self.rules
            .get(usize::from(category))?
            .get(usize::from(rule))
    }

    fn operator(&self, category: u16, text: &str) -> Option<&OperatorRows> {
        self.operators.get(usize::from(category))?.get(text)
    }

    fn infix_rows(&self, category: u16, text: &str) -> &[(u8, u8, u16, u16)] {
        self.operator(category, text)
            .map_or(&[], |row| row.infix.as_slice())
    }
    fn postfix_rows(&self, category: u16, text: &str) -> &[(u8, u16, u16)] {
        self.operator(category, text)
            .map_or(&[], |row| row.postfix.as_slice())
    }
    fn mixfix_rows(&self, category: u16, text: &str) -> &[(u8, u16, u16)] {
        self.operator(category, text)
            .map_or(&[], |row| row.mixfix.as_slice())
    }
    fn part(&self, category: u16, rule: u16, index: u8) -> Option<mixfix::MixfixPart<'_>> {
        let part = self.parts.get(&(category, rule))?.get(usize::from(index))?;
        Some((part.operand, &part.preceding, &part.following, part.capture))
    }
    fn parts_len(&self, category: u16, rule: u16) -> Option<u8> {
        if let Some(parts) = self.parts.get(&(category, rule)) {
            Some(u8::try_from(parts.len()).expect("descriptor mixfix part admission"))
        } else if self.row(category, rule)?.nullary.is_some() {
            Some(0)
        } else {
            None
        }
    }
    fn nullary(&self, category: u16, rule: u16) -> Option<&[&str]> {
        self.row(category, rule)?.nullary.as_deref()
    }

    fn lexical_prefix(&self, category: u16, kind: &TokenKind) -> Vec<LexAltRuleInfo> {
        let Some((buckets, order)) = self.descriptors.prefixes.get(usize::from(category)) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        // kind_dispatch emits rule-local matches in category declaration order.
        for rule in 0..self.rules[usize::from(category)].len() {
            let rule = u16::try_from(rule).expect("descriptor rule admission");
            if let Some(&(source, _, _)) = self.descriptors.transparent_projections.iter().find(
                |&&(_, result, projection_rule)| result == category && projection_rule == rule,
            ) {
                // The lexical emitter uses the source FIRST directly, before
                // unified-bucket Ident pruning, in its original returned order.
                for first in &self.descriptors.first_sets[usize::from(source)] {
                    if super::token_bindings::matches_prefix(
                        &first.pattern,
                        first.extra_guard.as_ref(),
                        kind,
                    ) {
                        out.push(LexAltRuleInfo {
                            rule_idx: rule,
                            kind: LexAltRuleKind::CrossCatProjection { source_src_idx: source },
                        });
                    }
                }
                continue;
            }
            for key in order {
                let bucket = &buckets[key];
                if !super::token_bindings::matches_prefix(
                    &bucket.pat,
                    bucket.extra_guard.as_ref(),
                    kind,
                ) {
                    continue;
                }
                for desc in &bucket.descs {
                    let (rule_idx, kind) = match desc {
                        UnifiedDescriptor::Atomic(arm) => (arm.rule_idx, LexAltRuleKind::Atomic),
                        UnifiedDescriptor::BinderPrefix { rule_idx, body_src_idx } => {
                            (*rule_idx, LexAltRuleKind::PrefixOp { body_src_idx: *body_src_idx })
                        },
                        UnifiedDescriptor::LeadingCategory { rule_idx, source_src_idx } => (
                            *rule_idx,
                            LexAltRuleKind::LeadingCategory { source_src_idx: *source_src_idx },
                        ),
                        UnifiedDescriptor::NullaryLiteralRun { rule_idx } => {
                            (*rule_idx, LexAltRuleKind::NullaryPrefixRun)
                        },
                        UnifiedDescriptor::CrossCatProjection { .. } => continue,
                        _ => unreachable!("constructor rejects unsupported prefix rows"),
                    };
                    if rule_idx == rule {
                        out.push(LexAltRuleInfo { rule_idx, kind });
                    }
                }
            }
        }
        out
    }

    fn primary_dispatch(&self, category: u16, kind: &TokenKind, non_atom: bool) -> bool {
        let TokenKind::Fixed(text) = kind else {
            return false;
        };
        // TerminalKeyword also has an original legacy-items form without a
        // syntax_pattern. Its atomic bucket is authoritative for that fixed
        // trigger; absence of authored syntax must not remove the keyword.
        if !non_atom {
            if let Some((buckets, order)) = self.descriptors.prefixes.get(usize::from(category)) {
                if order.iter().any(|key| {
                    let bucket = &buckets[key];
                    bucket
                        .descs
                        .iter()
                        .any(|desc| matches!(desc, UnifiedDescriptor::Atomic(_)))
                        && super::token_bindings::matches_prefix(
                            &bucket.pat,
                            bucket.extra_guard.as_ref(),
                            kind,
                        )
                }) {
                    return true;
                }
            }
        }
        self.rules.get(usize::from(category)).is_some_and(|rows| {
            rows.iter().any(|row| {
                row.trigger == Some(text.as_str())
                    && if non_atom {
                        row.binder.is_some() || row.nullary.is_some()
                    } else {
                        row.nullary.is_none()
                    }
            })
        })
    }

    fn leading_floor(&self, category: u16, rule: u16, caller: u8) -> Option<u8> {
        match self
            .descriptors
            .leading_binding_powers
            .get(&(category, rule))
        {
            None => Some(0),
            Some(powers) => (caller <= powers.entry).then_some(powers.left),
        }
    }

    fn prefix_lex(
        &self,
        pos: &usize,
        bp: &u8,
        top: Option<&WpdaGssNode>,
        tokens: &dyn WpdaTokenSource,
        frame: FrameCtx<'_>,
    ) -> Option<WpdaStepAction<LexicographicWeight>> {
        lexical_fork::prefix(
            self.primary,
            pos,
            bp,
            top,
            tokens,
            frame,
            |cat, rule, slot| self.collection_spec(cat, rule, slot),
            |cat, kind| self.lexical_prefix(cat, kind),
            |cat, rule, caller| self.leading_floor(cat, rule, caller),
            // Admission excludes every cross-category LHS row, so
            // these are the original empty policy tables, not missing evidence.
            |_, _, _| false,
            || {
                matches!(tokens.peek_kind(*pos), Some(TokenKind::Ident))
                    || tokens
                        .peek_alternatives(*pos)
                        .iter()
                        .any(|alt| matches!(alt.kind, TokenKind::Ident))
            },
            |_, _, _, _, _| true,
            |_, _, _, _, _| true,
            |_, _| false,
            |cat, kind| self.primary_dispatch(cat, kind, false),
            || {
                if self.contextual_keywords.is_empty() {
                    false
                } else {
                    tokens.peek_text(*pos).is_some_and(|text| {
                        self.contextual_keywords
                            .iter()
                            .any(|keyword| keyword == text)
                    })
                }
            },
            |_, _| false,
            |_, _, _| false,
            one,
            cost,
            lex_w_with_len,
            lex_w_alt_with_len,
            |open_len, cat, info| lex_w_alt_with_len(open_len, 0.0, cat, info.rule_idx, 0),
            |open_len, cat, info, alt| lex_w_alt_with_len(open_len, 0.0, cat, info.rule_idx, alt),
        )
    }

    fn prefix_route(
        &self,
        category: u16,
        pos: &usize,
        bp: &u8,
        top: Option<&WpdaGssNode>,
        tokens: &dyn WpdaTokenSource,
        peek: Option<TokenKind>,
    ) -> WpdaStepAction<LexicographicWeight> {
        if matches!(&peek, Some(TokenKind::Fixed(text)) if text == "(") {
            return self.paren(category, pos, bp, tokens);
        }
        // Generated category routing observes peek_kind again at its own site.
        let peek = tokens.peek_kind(*pos);
        if peek.is_none() {
            if let Some(route) = self.structural_hole_prefix_route(category, pos, bp, top) {
                return route;
            }
        }
        if let (Some(kind), Some((buckets, order))) =
            (peek, self.descriptors.prefixes.get(usize::from(category)))
        {
            for key in order {
                let bucket = &buckets[key];
                if !super::token_bindings::matches_prefix(
                    &bucket.pat,
                    bucket.extra_guard.as_ref(),
                    &kind,
                ) {
                    continue;
                }
                if let [desc] = bucket.descs.as_slice() {
                    if let UnifiedDescriptor::CrossCatProjection { source_src_idx, .. } = desc {
                        if !self.projection_compatible(*source_src_idx, tokens, *pos) {
                            continue;
                        }
                    }
                    if let UnifiedDescriptor::LeadingCategory { rule_idx, .. } = desc {
                        if self.leading_floor(category, *rule_idx, *bp).is_none() {
                            continue;
                        }
                    }
                    return match desc {
                        UnifiedDescriptor::Atomic(arm) => {
                            prefix::singleton_atomic(*bp, arm.category_src_idx, arm.rule_idx, cost)
                        },
                        UnifiedDescriptor::BinderPrefix { rule_idx, body_src_idx } => {
                            prefix::singleton_binder_prefix(
                                *bp,
                                category,
                                *rule_idx,
                                *body_src_idx,
                                cost,
                            )
                        },
                        UnifiedDescriptor::LeadingCategory { rule_idx, source_src_idx } => {
                            prefix::singleton_leading_category_with_floor(
                                *bp,
                                pos,
                                category,
                                *rule_idx,
                                *source_src_idx,
                                self.leading_floor(category, *rule_idx, *bp)
                                    .expect("checked leading admission"),
                                top.map(|node| node.symbol.kind),
                                cost,
                            )
                        },
                        UnifiedDescriptor::NullaryLiteralRun { rule_idx } => {
                            prefix::singleton_nullary_literal_run(bp, category, *rule_idx, cost)
                        },
                        UnifiedDescriptor::CrossCatProjection { rule_idx, source_src_idx } => {
                            prefix::singleton_crosscat_projection(
                                *bp,
                                bp,
                                category,
                                *rule_idx,
                                *source_src_idx,
                                cost,
                            )
                        },
                        _ => unreachable!("constructor rejects unsupported prefix rows"),
                    };
                }
                return prefix::unified_fork(bucket.descs.len(), |branches| {
                    for desc in &bucket.descs {
                        match desc {
                            UnifiedDescriptor::Atomic(arm) => prefix::push_atomic(
                                branches,
                                *bp,
                                arm.category_src_idx,
                                arm.rule_idx,
                                cost,
                            ),
                            UnifiedDescriptor::BinderPrefix { rule_idx, body_src_idx } => {
                                prefix::push_binder_prefix(
                                    branches,
                                    *bp,
                                    category,
                                    *rule_idx,
                                    *body_src_idx,
                                    cost,
                                )
                            },
                            UnifiedDescriptor::LeadingCategory { rule_idx, source_src_idx } => {
                                let Some(inner_bp) = self.leading_floor(category, *rule_idx, *bp)
                                else {
                                    continue;
                                };
                                prefix::push_leading_category_with_floor(
                                    branches,
                                    *bp,
                                    pos,
                                    category,
                                    *rule_idx,
                                    *source_src_idx,
                                    inner_bp,
                                    top.map(|node| node.symbol.kind),
                                    cost,
                                )
                            },
                            UnifiedDescriptor::NullaryLiteralRun { rule_idx } => {
                                prefix::push_nullary_literal_run(
                                    branches, bp, category, *rule_idx, cost,
                                )
                            },
                            UnifiedDescriptor::CrossCatProjection { rule_idx, source_src_idx } => {
                                if self.projection_compatible(*source_src_idx, tokens, *pos) {
                                    prefix::push_crosscat_projection(
                                        branches,
                                        *bp,
                                        bp,
                                        category,
                                        *rule_idx,
                                        *source_src_idx,
                                        cost,
                                    );
                                }
                            },
                            _ => unreachable!("constructor rejects unsupported prefix rows"),
                        }
                    }
                });
            }
        }
        WpdaStepAction::Error(format!("no prefix rule for category {category} at position {pos}"))
    }

    /// A structural FLT hole has no lexer token. Reuse the authored
    /// category-leading and transparent projection rows retained independently
    /// of token-FIRST buckets. Exact category admission and the existing
    /// reachability closure determine which sources may contain the hole;
    /// all eligible rule rows survive in authored rule order.
    fn structural_hole_prefix_route(
        &self,
        category: u16,
        pos: &usize,
        bp: &u8,
        top: Option<&WpdaGssNode>,
    ) -> Option<WpdaStepAction<LexicographicWeight>> {
        if !self.actions.supports_structural_holes() {
            return None;
        }
        let rows = self.descriptors.hole_prefixes.get(usize::from(category))?;
        let mut compatible = BTreeMap::new();
        let mut branches = Vec::new();
        for row in rows {
            let admits = *compatible
                .entry(row.source_src_idx)
                .or_insert_with(|| self.structural_hole_source_reachable(row.source_src_idx, *pos));
            if !admits {
                continue;
            }
            match row.kind {
                HolePrefixKind::LeadingCategory => {
                    let Some(inner_bp) = self.leading_floor(category, row.rule_idx, *bp) else {
                        continue;
                    };
                    prefix::push_leading_category_with_floor(
                        &mut branches,
                        *bp,
                        pos,
                        category,
                        row.rule_idx,
                        row.source_src_idx,
                        inner_bp,
                        top.map(|node| node.symbol.kind),
                        cost,
                    );
                },
                HolePrefixKind::CrossCatProjection => {
                    prefix::push_crosscat_projection(
                        &mut branches,
                        *bp,
                        bp,
                        category,
                        row.rule_idx,
                        row.source_src_idx,
                        cost,
                    );
                },
            }
        }
        (!branches.is_empty()).then_some(WpdaStepAction::Fork { branches, consume_trigger: false })
    }

    fn structural_hole_source_reachable(&self, source: u16, pos: usize) -> bool {
        self.actions.structural_hole_edge(source, pos).is_some()
            || self
                .descriptors
                .category_reachability
                .iter()
                .any(|&(from, to)| {
                    to == source && self.actions.structural_hole_edge(from, pos).is_some()
                })
    }

    fn projection_compatible(&self, source: u16, tokens: &dyn WpdaTokenSource, pos: usize) -> bool {
        crate::wpda_transitions::prefix_policy::crosscat_proj_lex_compatible(
            source,
            tokens,
            pos,
            |source| {
                self.descriptors
                    .projection_ident_var_only_sources
                    .contains(&source)
            },
        )
    }

    fn paren(
        &self,
        category: u16,
        pos: &usize,
        bp: &u8,
        tokens: &dyn WpdaTokenSource,
    ) -> WpdaStepAction<LexicographicWeight> {
        let Some(rows) = self.rules.get(usize::from(category)) else {
            return WpdaStepAction::Error(format!("unknown category {category}"));
        };
        let local_paren = rows
            .iter()
            .any(|row| row.binder.is_some() && row.trigger == Some("("));
        let original_sources = &self.descriptors.grouping_sources[usize::from(category)];
        if !local_paren && original_sources.len() == 1 {
            return prefix::paren_singleton(original_sources[0], bp, pos, tokens, one);
        }
        let sources = if local_paren {
            vec![category]
        } else {
            original_sources.clone()
        };
        let binders: Vec<_> = sources
            .iter()
            .flat_map(|&owner| {
                self.rules[usize::from(owner)]
                    .iter()
                    .enumerate()
                    .filter_map(move |(rule, row)| {
                        row.binder
                            .as_ref()
                            .filter(|_| row.trigger == Some("("))
                            .map(|shape| (owner, rule, shape))
                    })
            })
            .collect();
        prefix::paren_fork(sources.len() + binders.len(), |branches| {
            for source in sources {
                branches.push(prefix::paren_grouping_branch(
                    source,
                    bp,
                    pos,
                    tokens,
                    || {
                        if source == category {
                            one()
                        } else {
                            cost(
                                crate::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
                                source,
                                0,
                            )
                        }
                    },
                    || {
                        if source == category {
                            ForkActionKind::ConsumeAndPush { trigger_mode: TriggerMode::Discard }
                        } else {
                            ForkActionKind::ConsumeAndPushCrossCatLhs {
                                trigger_mode: TriggerMode::Discard,
                            }
                        }
                    },
                ));
            }
            for (owner, rule, shape) in binders {
                let rule = u16::try_from(rule).expect("descriptor rule admission");
                let body = binder_initial_body_cat(shape)
                    .and_then(|name| self.category_index(name))
                    .unwrap_or(owner);
                branches.push(prefix::paren_binder_branch(
                    owner,
                    rule,
                    body,
                    *bp,
                    || {
                        if owner == category {
                            StackSymbolV2::rule_at(owner, rule, 1, Some(*bp))
                        } else {
                            StackSymbolV2::category_entry(owner)
                        }
                    },
                    || {
                        cost(
                            if owner == category {
                                0.0
                            } else {
                                crate::automata::lex_weight::BP_TIER_CROSSCAT_LHS
                            },
                            owner,
                            rule,
                        )
                    },
                    || {
                        if owner == category {
                            ForkActionKind::ConsumeAndPush {
                                trigger_mode: TriggerMode::ConsumeAsTriggerOnly,
                            }
                        } else {
                            ForkActionKind::PushCrossCatLhs
                        }
                    },
                ));
            }
        })
    }

    fn category_index(&self, name: &str) -> Option<u16> {
        self.descriptors
            .synthesis
            .categories
            .iter()
            .position(|category| category == name)
            .and_then(|index| u16::try_from(index).ok())
    }

    fn collection_element_can_start(&self, category: u16, kind: &TokenKind) -> bool {
        self.descriptors
            .first_sets
            .get(usize::from(category))
            .is_some_and(|rows| {
                rows.iter().any(|row| {
                    super::token_bindings::matches_prefix(
                        &row.pattern,
                        row.extra_guard.as_ref(),
                        kind,
                    )
                })
            })
    }

    fn binder_step(
        &self,
        category: &u16,
        rule: &u16,
        body: &u16,
        bp: &u8,
        top: Option<&WpdaGssNode>,
        pos: usize,
        tokens: &dyn WpdaTokenSource,
    ) -> WpdaStepAction<LexicographicWeight> {
        if let Some(entry) = top.filter(|entry| entry.symbol.kind == SymbolKind::CategoryEntry) {
            return binder::category_entry_prelude(
                entry,
                category,
                rule,
                body,
                bp,
                pos,
                tokens,
                || {
                    self.row(*category, *rule)
                        .filter(|row| row.binder.is_some())
                        .and_then(|row| row.trigger)
                },
                one,
            );
        }
        let Some(node) = top else {
            return WpdaStepAction::Idle;
        };
        let SymbolKind::RuleAt(position) = node.symbol.kind else {
            return WpdaStepAction::Idle;
        };
        let Some(shape) = self
            .row(*category, *rule)
            .and_then(|row| row.binder.as_ref())
        else {
            return WpdaStepAction::Idle;
        };
        if usize::from(position) == shape.positions.len() + 1 {
            return binder::rule_complete(*bp, one);
        }
        let Some(index) = usize::from(position).checked_sub(1) else {
            return WpdaStepAction::Idle;
        };
        let Some(item) = shape.positions.get(index) else {
            return WpdaStepAction::Idle;
        };
        let next = position + 1;
        match item {
            BinderPosition::Literal(text) => binder::rule_literal(
                *category,
                *rule,
                next,
                *bp,
                *body,
                text,
                required_top_cat_after_position(
                    index
                        .checked_sub(1)
                        .and_then(|previous| shape.positions.get(previous)),
                    &self.descriptors.synthesis.categories,
                ),
                one,
            ),
            BinderPosition::ParamParse { cat, collection: None } => binder::rule_parameter(
                *category,
                *rule,
                next,
                *bp,
                self.category_index(cat).expect("admitted operand category"),
                pos,
                self.descriptors
                    .leading_binding_powers
                    .get(&(*category, *rule))
                    .map(|powers| powers.right)
                    .or_else(|| {
                        self.descriptors
                            .prefix_binding_powers
                            .get(&(*category, *rule))
                            .copied()
                    })
                    .unwrap_or(0),
                one,
            ),
            BinderPosition::ParamParse { collection: Some(info), .. } => {
                binder::rule_collection_parameter(
                    *category,
                    *rule,
                    next,
                    *bp,
                    info.slot_idx,
                    pos,
                    one,
                )
            },
            BinderPosition::IdentTextCapture { .. } | BinderPosition::TokenKindCapture { .. } => {
                let name = match item {
                    BinderPosition::TokenKindCapture { kind_name, .. } => kind_name.as_str(),
                    _ => "Ident",
                };
                binder::token_capture_and_replace(
                    tokens,
                    pos,
                    name,
                    || StackSymbolV2::rule_at(*category, *rule, next, Some(*bp)),
                    || WpdaState::BinderRule {
                        result_src_idx: *category,
                        rule_idx: *rule,
                        body_src_idx: *body,
                        outer_bp: *bp,
                    },
                    lex_w_alt_with_len,
                )
            },
            _ => unreachable!("constructor rejects unsupported binder positions"),
        }
    }
}

impl<P> WpdaEngine<LexicographicWeight> for OwnedWpdaEngine<'_, P> {
    fn step(
        &self,
        state: &WpdaState,
        _gss: &WpdaGss<LexicographicWeight>,
        top: Option<&WpdaGssNode>,
        pos: usize,
        tokens: &dyn WpdaTokenSource,
        frame: FrameCtx<'_>,
    ) -> WpdaStepAction<LexicographicWeight> {
        match state {
            WpdaState::Ready { min_bp } => control::ready(self.primary, min_bp, cost),
            WpdaState::PrefixDispatch { pos, cur_bp } => prefix_dispatch::prefix_dispatch(self.primary, pos, cur_bp, top, tokens,
                || self.prefix_lex(pos, cur_bp, top, tokens, frame), |cat, rule, slot| self.collection_spec(cat, rule, slot), |cat, kind| self.collection_element_can_start(cat, kind), cost,
                |category, _, peek| self.prefix_route(category, pos, cur_bp, top, tokens, peek)),
            WpdaState::EnterLeadingChild { source_src_idx, inner_bp } =>
                prefix::enter_leading_child(*source_src_idx, *inner_bp, pos, one),
            WpdaState::Unwinding => unwinding::unwinding_step(self, top, pos, tokens, one,
                |cat, text| self.category_recognizes_operator(cat, text),
                |cat, rule| self.parts_len(cat, rule), |cat, rule, part| self.part(cat, rule, part),
                |_| None, |_, _, _, _| None, |_| None),
            WpdaState::InfixLoop { cur_bp } => infix::infix_loop::<_, false>(self.primary, cur_bp, top, pos, tokens,
                |cat, rule, slot| self.collection_spec(cat, rule, slot), |from, to| from == to || self.descriptors.category_reachability.contains(&(from, to)),
                |cat| lexical_fork::infix(cat, cur_bp, pos, tokens, frame,
                    |cat, kind| match kind { TokenKind::Fixed(text) => self.operator(cat, text).map_or_else(Vec::new, |row| row.lexical.clone()), _ => Vec::new() },
                    |_, info| info.rule_idx, lex_w_alt, one),
                |cat, text| self.infix_rows(cat, text), |cat, text| self.postfix_rows(cat, text), |cat, text| self.mixfix_rows(cat, text),
                |cat, rule, part| self.part(cat, rule, part), |cat, rule| self.nullary(cat, rule),
                |cat, result, rule| self.absorption.get(&(cat, result, rule)).copied().flatten(), cost,
                |_, _, rows, fallback, goal, method, branches| { mixfix::member_fan(rows, cur_bp, fallback, goal, method, cost, branches); false }),
            WpdaState::InfixChainIterative { rhs_bp, .. } => control::infix_chain_iterative(rhs_bp, pos),
            WpdaState::MixfixContinuation { result_src_idx, rule_idx, completed_idx } => mixfix::continuation(result_src_idx, rule_idx, completed_idx, top, pos,
                |cat, rule, part| self.part(cat, rule, part), one),
            WpdaState::MixfixLiteralRun { result_src_idx, rule_idx, completed_idx, kind, sub_pos } => {
                let bp = top.filter(|node| node.symbol.kind == SymbolKind::MixfixMarker).and_then(|node| node.symbol.continuation_bp)
                    .expect("MixfixLiteralRun invariant: frontier top must carry its continuation floor");
                mixfix::literal_run(result_src_idx, rule_idx, completed_idx, kind, sub_pos, bp, pos, tokens, one,
                    |cat, rule, part| self.part(cat, rule, part), |cat, rule| self.parts_len(cat, rule), |_, _, _| None,
                    |cat, rule| self.nullary(cat, rule))
            },
            WpdaState::BinderRule { result_src_idx, rule_idx, body_src_idx, outer_bp } => self.binder_step(result_src_idx, rule_idx, body_src_idx, outer_bp, top, pos, tokens),
            WpdaState::CrossCatDelegate { source_src_idx, inner_cur_bp } => control::cross_category_delegate(source_src_idx, inner_cur_bp, pos, one),
            WpdaState::GroupingClosePreservingInner { inner_cat_src_idx } => control::grouping_close(inner_cat_src_idx, top, pos, tokens, one),
            WpdaState::CollectionOpenParen { result_src_idx, rule_idx, element_src_idx, outer_bp } => control::collection_open_paren(result_src_idx, rule_idx, element_src_idx, outer_bp, pos, tokens, one),
            WpdaState::AmbiguityFanout { .. } => WpdaStepAction::Error("engine.step called with AmbiguityFanout; walker should drive this state via step_fanout".into()),
            WpdaState::CollectionLoop { result_src_idx, rule_idx, element_src_idx, outer_bp, accumulator_id, slot_idx, kv_phase } => collection_loop::collection_loop_step(self, result_src_idx, rule_idx, element_src_idx, outer_bp, accumulator_id, slot_idx, kv_phase, pos, tokens, cost, |cat, kind| self.collection_element_can_start(cat, kind)),
            WpdaState::BinderListLoop { .. } | WpdaState::OptionalGroup { .. } => WpdaStepAction::Error("state is outside the admitted owned routing domain".into()),
            WpdaState::Saturating { .. } | WpdaState::Accepted | WpdaState::Error { .. } => WpdaStepAction::Idle,
        }
    }
    fn action_signature(&self, category: u16, rule: u16) -> Option<ActionSignature<'_>> {
        self.actions.action_signature(category, rule)
    }
    fn grouping_boundary_rule(&self) -> Option<u32> {
        self.actions.grouping_boundary_rule()
    }
    fn structural_hole_edge(&self, category: u16, pos: usize) -> Option<(usize, u32)> {
        self.actions.structural_hole_edge(category, pos)
    }
    fn supports_structural_holes(&self) -> bool {
        self.actions.supports_structural_holes()
    }
    fn execute_action(
        &self,
        category: u16,
        rule: u16,
        builder: &mut SemanticBuilder,
        args: Vec<ActionArg>,
    ) -> Result<(), ActionInvocationError> {
        self.actions.execute_action(category, rule, builder, args)
    }
    fn execute_action_with_context(
        &self,
        category: u16,
        rule: u16,
        builder: &mut SemanticBuilder,
        args: Vec<ActionArg>,
        context: crate::wpda_runtime::ActionContext,
    ) -> Result<(), ActionInvocationError> {
        self.actions
            .execute_action_with_context(category, rule, builder, args, context)
    }
    fn term_category(&self, value: &(dyn Any + Send + Sync), _: &str) -> Option<u16> {
        self.actions.term_category(value)
    }
    fn semantic_content_key(
        &self,
        term: &std::sync::Arc<dyn Any + Send + Sync>,
        cache: &mut mettail_semantic_key::ContentKeyCache,
    ) -> Result<Option<mettail_semantic_key::ContentKey>, mettail_semantic_key::ContentKeyCacheError>
    {
        self.actions.semantic_content_key(term, cache)
    }
    fn rule_has_leading_structural_trigger(&self, category: u16, rule: u16) -> bool {
        self.row(category, rule)
            .is_some_and(|row| row.leading_literal)
    }
    fn rule_leads_with_literal(&self, category: u16, rule: u16) -> bool {
        self.row(category, rule)
            .is_some_and(|row| row.leading_literal)
    }
    fn min_terminal_span(&self, category: u16, rule: u16) -> u32 {
        self.row(category, rule)
            .map_or(0, |row| row.min_terminal_span)
    }
    fn category_is_binder_scoped(&self, _: u16) -> bool {
        false
    }
    fn collection_spec(
        &self,
        category: u16,
        rule: u16,
        slot: u8,
    ) -> Option<crate::wpda_runtime::CollectionSpec<'_>> {
        self.descriptors
            .collections
            .iter()
            .find(|row| row.key == (category, rule, slot))
            .map(|row| row.spec.as_borrowed())
    }
    fn kv_separator_for_collection(&self, category: u16, rule: u16, slot: u8) -> Option<&str> {
        self.collection_spec(category, rule, slot)
            .and_then(|spec| spec.kv_sep)
    }
    fn collection_element_src_idx(&self, category: u16, rule: u16, slot: u8) -> Option<u16> {
        self.collection_spec(category, rule, slot)
            .and_then(|spec| spec.element_src_idx)
    }
    fn is_binder_internal_collection(&self, category: u16, rule: u16) -> bool {
        self.row(category, rule)
            .and_then(|row| row.binder.as_ref())
            .is_some_and(|shape| has_binder_internal_collection_slot(&shape.positions))
    }
    fn chain_atom_rules_for_token(
        &self,
        category: u16,
        kind: &TokenKind,
        _: Option<&str>,
    ) -> Vec<u16> {
        self.lexical_prefix(category, kind)
            .into_iter()
            .filter_map(|info| matches!(info.kind, LexAltRuleKind::Atomic).then_some(info.rule_idx))
            .collect()
    }
    fn chain_atom_producers_for_token(
        &self,
        category: u16,
        kind: &TokenKind,
        text: Option<&str>,
    ) -> Vec<crate::wpda_walker::ChainAtomProducer> {
        let mut out = self
            .chain_atom_rules_for_token(category, kind, text)
            .into_iter()
            .map(|rule| crate::wpda_walker::ChainAtomProducer::direct(category, rule))
            .collect::<Vec<_>>();
        for &(from, to, wrapper) in &self.descriptors.transparent_projections {
            if to != category {
                continue;
            }
            for atom in self.chain_atom_rules_for_token(from, kind, text) {
                out.push(crate::wpda_walker::ChainAtomProducer::projected(from, atom, wrapper));
            }
        }
        out
    }
    fn single_hop_coercion(&self, from: u16, to: u16) -> &[(u16, u16)] {
        self.descriptors
            .single_hop_coercions
            .get(&(from, to))
            .map_or(&[], Vec::as_slice)
    }
    fn single_hop_coercion_weight(
        &self,
        from_cat: u16,
        to_cat: u16,
        coercion_cat: u16,
        rule_idx: u16,
        span_len: u32,
    ) -> LexicographicWeight {
        let _ = (from_cat, to_cat);
        if coercion_cat == to_cat {
            cost(
                crate::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION
                    * f64::from(span_len.max(1)),
                coercion_cat,
                rule_idx,
            )
        } else {
            one()
        }
    }
    fn single_hop_coercion_completion_weight(
        &self,
        from_cat: u16,
        to_cat: u16,
        coercion_cat: u16,
        rule_idx: u16,
        span_len: u32,
    ) -> LexicographicWeight {
        let _ = (from_cat, to_cat);
        let extra_span = span_len.saturating_sub(1);
        if coercion_cat == to_cat && extra_span > 0 {
            cost(
                crate::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION * f64::from(extra_span),
                coercion_cat,
                rule_idx,
            )
        } else {
            one()
        }
    }
    fn fork_emission_ordinal(&self, site: u8, category: u16, rule: u16) -> u16 {
        match site {
            0 => 0,
            1 | 3 => 1,
            2 => self
                .fork_ordinals
                .site2_ordinal(category, rule)
                .unwrap_or(0),
            _ => u16::MAX,
        }
    }
    fn parikh_class_of(&self, kind: &TokenKind) -> Option<u8> {
        let alphabet = &self.descriptors.parikh.alphabet;
        Some(match kind {
            TokenKind::Fixed(text) => alphabet.class_of_terminal(text),
            _ => alphabet.coarse_bit,
        })
    }
    fn parikh_must_mask(&self, category: u16, rule: u16, position: u8) -> u128 {
        self.descriptors
            .parikh
            .must_entries
            .get(&(category, rule, position))
            .copied()
            .unwrap_or(0)
    }
    fn is_structural_open_delimiter(&self, kind: &TokenKind, text: Option<&str>) -> bool {
        matches!(kind, TokenKind::Fixed(value) if self.descriptors.structural_delimiters.0.contains(value))
            || text.is_some_and(|text| self.descriptors.structural_delimiters.0.contains(text))
    }
    fn is_structural_close_delimiter(&self, kind: &TokenKind, text: Option<&str>) -> bool {
        matches!(kind, TokenKind::Fixed(value) if self.descriptors.structural_delimiters.1.contains(value))
            || text.is_some_and(|text| self.descriptors.structural_delimiters.1.contains(text))
    }
    fn category_recognizes_operator(&self, category: u16, text: &str) -> bool {
        control::operator_recognized(
            || self.infix_rows(category, text),
            || self.postfix_rows(category, text),
            || self.mixfix_rows(category, text),
        )
    }
    fn category_accepts_operator_at_floor(&self, category: u16, text: &str, floor: u8) -> bool {
        control::operator_at_floor(
            floor,
            || self.infix_rows(category, text),
            || self.postfix_rows(category, text),
            || self.mixfix_rows(category, text),
        )
    }
    fn prefix_token_has_non_atom_start(
        &self,
        category: u16,
        kind: &TokenKind,
        _: Option<&str>,
    ) -> bool {
        control::prefix_token_has_non_atom_start(
            category,
            kind,
            |cat, kind| self.lexical_prefix(cat, kind),
            |cat, kind| self.primary_dispatch(cat, kind, true),
            |_, _| false,
        )
    }
}
