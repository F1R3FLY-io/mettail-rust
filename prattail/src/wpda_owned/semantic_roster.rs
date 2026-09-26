//! Checked borrowed observations for the original typed-AST variant roster.
//!
//! Source map: `subst::collect_category_variants` supplies the shared assembly;
//! `rule_to_variant_kind` reads Var/Literal first, then capture/context/items.
//! This adapter admits only capture-free Simple(Base)/Simple(List(Base)) source
//! contexts. In that subset `field_infos_from_term_param` emits one field per
//! parameter, in order; `variant_kind_from_term_context` chooses Nullary,
//! Regular, or the single Collection arm. No other shape is inferred here.
//! The transparent check is the exact admitted SimpleProjectionShape predicate
//! in ast/grammar_shapes.rs: one Simple(Base) parameter, one matching Param,
//! and unequal categories. Ranked rows are additionally refused as transparent.
//! Original semantic_hash builds its transparent-label set across categories;
//! duplicate authored labels across categories therefore make this per-row
//! profile unavailable. The original global macro behavior is left unchanged.
//!
//! Unsupported observations return no key profile, never remove parser rows.
//! The checked ReductionPlan/source-slot correspondence is part of admission;
//! neither WPDA rule indices nor global semantic discriminants provide tags.

use crate::wpda_rule_analysis::{
    authored::AuthoredRuleReader, authored_action::authored_action_categories,
    authored_descriptors::OwnedWpdaDescriptors,
};
use mettail_grammar_core::{
    term_param_walk::try_declares_binder, variant_roster::complete_category_variants,
    AuthoredLegacyItem, AuthoredNameId, AuthoredNode, AuthoredParam, AuthoredRule,
    AuthoredRuleStore, AuthoredSyntax, AuthoredType, CategoryId, CollectionKind, ConstructorId,
    FieldSource, GrammarCoreV1, NativeKind, NonTerminalKind, Production, SourceObservation,
    SyntaxItem,
};
use std::collections::BTreeMap;
use std::convert::Infallible;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SemanticFieldKind {
    Term,
    OrderedList,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticField {
    pub category: CategoryId,
    pub kind: SemanticFieldKind,
}

#[derive(Debug)]
pub struct SemanticConstructor {
    pub local_tag: u8,
    pub transparent: bool,
    pub fields: Vec<SemanticField>,
}

#[derive(Debug)]
pub struct SemanticCategory {
    pub category: CategoryId,
    pub native: Option<NativeKind>,
    pub literal_tag: Option<u8>,
    pub variable: bool,
}

#[derive(Debug)]
pub struct OwnedSemanticRoster {
    /// Same order as the original WPDA category census, not Core ID order.
    pub categories: Vec<SemanticCategory>,
    pub constructors: BTreeMap<(CategoryId, ConstructorId), SemanticConstructor>,
}

#[derive(Clone, Copy)]
enum Variant {
    Authored(usize),
    Var,
    Literal,
}

fn name(store: &AuthoredRuleStore, id: AuthoredNameId) -> Option<&str> {
    match store.get(id.0)? {
        AuthoredNode::Name(name) => Some(&name.spelling),
        _ => None,
    }
}

fn collection_slot(item: &SyntaxItem) -> Option<(&str, CategoryId)> {
    let inner = match item {
        SyntaxItem::Separated { source, .. } => source.as_ref(),
        item => item,
    };
    match inner {
        SyntaxItem::Collection {
            slot,
            key: None,
            element,
            kind: CollectionKind::List,
            ..
        } => Some((slot, *element)),
        _ => None,
    }
}

/// A checked subset of the original field observer, not general normalization.
fn constructor_fields(
    store: &AuthoredRuleStore,
    rule: &AuthoredRule,
    production: &Production,
    categories: &BTreeMap<&str, CategoryId>,
) -> Option<(Vec<SemanticField>, bool)> {
    if rule.source_body_present != SourceObservation::Known(false)
        || rule.explicit_fold != SourceObservation::Known(false)
    {
        return None;
    }
    let AuthoredNode::Params(params) = store.get(rule.term_context?.0)? else {
        return None;
    };
    // Reject capture arms before observing context fields, as the original
    // rule_to_variant_kind checks capture_layout before the context arm.
    let AuthoredNode::Syntax(syntax) = store.get(rule.syntax_pattern?.0)? else {
        return None;
    };
    if syntax.iter().any(|item| {
        matches!(item, AuthoredSyntax::TokenKind { .. } | AuthoredSyntax::GuestBody { .. })
    }) {
        return None;
    }
    let slots: Vec<_> = production
        .syntax
        .iter()
        .filter(|item| !matches!(item, SyntaxItem::Token(_)))
        .collect();
    if slots.len() != params.len() {
        return None;
    }
    let mut fields = Vec::with_capacity(params.len());
    let mut sole_parameter = None;
    for (param, slot) in params.iter().zip(slots) {
        let AuthoredNode::Param(AuthoredParam::Simple { name: param_name, ty }) =
            store.get(param.0)?
        else {
            return None;
        };
        let param_name = name(store, *param_name)?;
        let (category_name, kind) = match store.get(ty.0)? {
            AuthoredNode::Type(AuthoredType::Base(category)) => {
                (name(store, *category)?, SemanticFieldKind::Term)
            },
            AuthoredNode::Type(AuthoredType::Collection {
                kind: CollectionKind::List,
                element,
            }) => {
                let AuthoredNode::Type(AuthoredType::Base(category)) = store.get(element.0)? else {
                    return None;
                };
                (name(store, *category)?, SemanticFieldKind::OrderedList)
            },
            _ => return None,
        };
        let category = *categories.get(category_name)?;
        match kind {
            SemanticFieldKind::Term => {
                if !matches!(slot, SyntaxItem::Category { category: actual, slot }
                    if *actual == category && slot == param_name)
                {
                    return None;
                }
            },
            SemanticFieldKind::OrderedList => {
                if collection_slot(slot)? != (param_name, category) {
                    return None;
                }
            },
        }
        fields.push(SemanticField { category, kind });
        sole_parameter = Some((param_name, category_name, kind));
    }
    let transparent = if let (
        [_],
        [AuthoredSyntax::Param(parameter)],
        Some((param, source, SemanticFieldKind::Term)),
    ) = (params.as_slice(), syntax.as_slice(), sole_parameter)
    {
        source != name(store, rule.category)? && name(store, *parameter)? == param
    } else {
        false
    };
    if transparent && production.precedence.binding_power.is_some() {
        return None;
    }
    Some((fields, transparent))
}

/// The caller's existing descriptor/action admission prepays this finite view.
/// A missing or unsupported source observation is explicitly unavailable.
pub fn derive<P>(
    core: &GrammarCoreV1,
    descriptors: &OwnedWpdaDescriptors<P>,
) -> Option<OwnedSemanticRoster> {
    let core_categories = authored_action_categories(core, descriptors).ok()?;
    derive_roster(core, &descriptors.original_occurrences, &core_categories)
}

fn derive_roster(
    core: &GrammarCoreV1,
    occurrences: &[usize],
    core_categories: &[CategoryId],
) -> Option<OwnedSemanticRoster> {
    let store = core.authored.as_ref()?;
    let header = store.declarations()?;
    let bindings = core.authored_bindings.as_ref()?;
    if header.categories.len() != bindings.categories.len() {
        return None;
    }
    let reader = AuthoredRuleReader::new(store).ok()?;
    let rules = occurrences
        .iter()
        .map(|&index| core.productions.get(index)?.authored)
        .collect::<Option<Vec<_>>>()?;
    // semantic_hash.rs's transparent_labels is global by source label spelling.
    // Per-row transparency is equivalent only in this checked unique-category
    // label domain. Refuse the key profile, not any production or parse reading.
    let mut label_categories = BTreeMap::new();
    for rule_id in &rules {
        let AuthoredNode::Rule(rule) = store.get(rule_id.0)? else {
            return None;
        };
        let category = name(store, rule.category)?;
        if label_categories
            .insert(name(store, rule.label)?, category)
            .is_some_and(|previous| previous != category)
        {
            return None;
        }
    }
    // Reuse the original HOL demand gate; no binder means no HOL variants.
    if try_declares_binder(&reader, rules.iter().copied(), |_| Ok::<_, Infallible>(())).ok()? {
        return None;
    }
    let categories = header
        .categories
        .iter()
        .zip(&bindings.categories)
        .map(|(source, &bound)| Some((name(store, source.name)?, bound)))
        .collect::<Option<BTreeMap<_, _>>>()?;
    let mut output = OwnedSemanticRoster {
        categories: Vec::new(),
        constructors: BTreeMap::new(),
    };
    for &category in core_categories {
        let source_index = bindings
            .categories
            .iter()
            .position(|&bound| bound == category)?;
        let declaration = &header.categories[source_index];
        let SourceObservation::Known(data_role) = declaration.data_observation else {
            return None;
        };
        if declaration.byte_observation != SourceObservation::Known(false)
            || declaration.element_observation != SourceObservation::Known(None)
            || declaration.native.is_some_and(|kind| {
                !kind.is_integer() && !matches!(kind, NativeKind::Str | NativeKind::Bool)
            })
        {
            return None;
        }
        let mut authored = Vec::new();
        for (&index, &rule_id) in occurrences.iter().zip(&rules) {
            let production = &core.productions[index];
            if production.result != category {
                continue;
            }
            let AuthoredNode::Rule(rule) = store.get(rule_id.0)? else {
                return None;
            };
            if categories.get(name(store, rule.category)?).copied() != Some(category) {
                return None;
            }
            // Explicit Var/Literal AST arms need a dedicated execution relation;
            // the supported native leaf relation is the original implicit arm.
            if matches!(rule.items.as_slice(), [AuthoredLegacyItem::NonTerminal { kind, .. }]
                if *kind == NonTerminalKind::Var || kind.is_literal())
            {
                return None;
            }
            authored.push(Variant::Authored(index));
        }
        let roster = complete_category_variants(
            authored,
            |variant| matches!(variant, Variant::Var),
            || !data_role,
            || Variant::Var,
            |variants| {
                if declaration.native.is_some() {
                    variants.push(Variant::Literal);
                }
            },
            |_| {}, // Original declares_binder gate above proved the HOL roster empty.
        );
        // Original semantic_hash refuses more than 255 category-local variants.
        if roster.len() > usize::from(u8::MAX) {
            return None;
        }
        let mut summary = SemanticCategory {
            category,
            native: declaration.native,
            literal_tag: None,
            variable: false,
        };
        for (index, variant) in roster.into_iter().enumerate() {
            let local_tag = u8::try_from(index).ok()?;
            match variant {
                Variant::Var => summary.variable = true,
                Variant::Literal => summary.literal_tag = Some(local_tag),
                Variant::Authored(index) => {
                    let production = &core.productions[index];
                    let AuthoredNode::Rule(rule) = store.get(production.authored?.0)? else {
                        return None;
                    };
                    let (fields, transparent) =
                        constructor_fields(store, rule, production, &categories)?;
                    let plan = core.reductions.get(production.reduction as usize)?;
                    if plan.output_category != category || plan.constructor != production.constructor
                        || usize::from(plan.input_arity) != fields.len()
                        || plan.fields.len() != fields.len() || plan.evaluation.is_some()
                        || plan.fields.iter().enumerate().any(|(index, field)|
                            !matches!(field, FieldSource::Input(input) if usize::from(*input) == index))
                    { return None; }
                    if output
                        .constructors
                        .insert(
                            (category, production.constructor),
                            SemanticConstructor { local_tag, transparent, fields },
                        )
                        .is_some()
                    {
                        return None;
                    }
                },
            }
        }
        output.categories.push(summary);
    }
    Some(output)
}

#[cfg(test)]
mod tests;
