//! Original collection descriptor discovery shared by generated and owned engines.
//!
//! The enclosing assembly admits the complete helper domain before these workers.
//! Callback errors stop immediately; a conflicting table discovery instead freezes
//! insertion while the original remaining observations continue.

use super::CollectionShape;
use crate::binding_power::InfixRuleInfo;
use crate::wpda_rule_analysis::binder::{BinderPosition, BinderShape, CollectionSepInfo};
use mettail_ast::types::CollectionType;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub type CollectionSpecKey = (u16, u16, u8);
pub type MixfixRepSlot = (u8, String, String, Vec<String>, u8);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneratedCollectionSpec {
    pub open: String,
    pub has_synth_paren: bool,
    pub close: String,
    pub sep: String,
    pub min_elements: u8,
    pub kv_sep: Option<String>,
    pub kv_value_optional: bool,
    pub element_src_idx: Option<u16>,
    pub close_resumes_via_unwinding: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneratedCollectionSpecArm {
    pub key: CollectionSpecKey,
    pub spec: GeneratedCollectionSpec,
    pub first_origin: String,
}

/// Borrowed original observations; labels are read only at insertion sites.
pub trait CollectionAssemblyContext<'source, Rule: 'source> {
    type Error;
    type Label: fmt::Display;
    fn try_infix(&mut self, rule: &'source Rule) -> Result<Option<InfixRuleInfo>, Self::Error>;
    fn try_collection(
        &mut self,
        rule: &'source Rule,
    ) -> Result<Option<CollectionShape<CollectionType>>, Self::Error>;
    fn try_binder(&mut self, rule: &'source Rule) -> Result<Option<BinderShape>, Self::Error>;
    fn try_label(&mut self, rule: &'source Rule) -> Result<Self::Label, Self::Error>;
}

#[derive(Debug, PartialEq, Eq)]
pub enum CollectionAssemblyError<E> {
    Callback(E),
    CategoryIndex { index: usize },
    RuleIndex { index: usize },
    ElementCategoryIndex { index: usize },
    MixfixPartIndex { index: usize },
    Conflict(String),
}

impl<E: fmt::Display> fmt::Display for CollectionAssemblyError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Callback(error) => error.fmt(f),
            Self::CategoryIndex { index } => {
                write!(f, "collection category index {index} exceeds u16")
            },
            Self::RuleIndex { index } => write!(f, "collection rule index {index} exceeds u16"),
            Self::ElementCategoryIndex { index } => {
                write!(f, "collection element category index {index} exceeds u16")
            },
            Self::MixfixPartIndex { index } => {
                write!(f, "collection repetition part index {index} exceeds u8")
            },
            Self::Conflict(message) => message.fmt(f),
        }
    }
}
impl<E: std::error::Error + 'static> std::error::Error for CollectionAssemblyError<E> {}

/// The original checked insertion; equal duplicates retain their first origin.
pub fn insert_collection_spec_arm(
    arms: &mut Vec<GeneratedCollectionSpecArm>,
    indices: &mut BTreeMap<CollectionSpecKey, usize>,
    key: CollectionSpecKey,
    spec: GeneratedCollectionSpec,
    origin: String,
) -> Result<(), String> {
    if let Some(&index) = indices.get(&key) {
        let existing = &arms[index];
        if existing.spec == spec {
            return Ok(());
        }
        return Err(format!(
            "conflicting generated CollectionSpec for key {key:?}: first from {} as {:?}; \
             conflicting discovery from {origin} as {spec:?}",
            existing.first_origin, existing.spec,
        ));
    }
    indices.insert(key, arms.len());
    arms.push(GeneratedCollectionSpecArm { key, spec, first_origin: origin });
    Ok(())
}

fn collect_binder_collection_infos<'a>(
    positions: &'a [BinderPosition],
    out: &mut Vec<&'a CollectionSepInfo>,
) {
    let mut work: Vec<&BinderPosition> = positions.iter().rev().collect();
    while let Some(position) = work.pop() {
        match position {
            BinderPosition::ParamParse { collection: Some(info), .. } => out.push(info),
            BinderPosition::OptionalGroup { positions: inner_positions, .. } => {
                work.extend(inner_positions.iter().rev());
            },
            _ => {},
        }
    }
}
pub fn binder_collection_infos(shape: &BinderShape) -> Vec<&CollectionSepInfo> {
    let mut infos = Vec::new();
    collect_binder_collection_infos(&shape.positions, &mut infos);
    infos
}

pub fn try_lookup_element_src_idx<E>(
    element_cat: &str,
    categories: &[String],
) -> Result<Option<u16>, CollectionAssemblyError<E>> {
    categories
        .iter()
        .position(|c| c == element_cat)
        .map(|index| {
            u16::try_from(index)
                .map_err(|_| CollectionAssemblyError::ElementCategoryIndex { index })
        })
        .transpose()
}

pub fn try_mixfix_rep_slots<'source, Rule: 'source, C>(
    rule: &'source Rule,
    context: &mut C,
) -> Result<Vec<MixfixRepSlot>, CollectionAssemblyError<C::Error>>
where
    C: CollectionAssemblyContext<'source, Rule>,
{
    try_mixfix_rep_slots_with(|| context.try_infix(rule))
}

/// Standalone original infix probe, also used by macro callers without a language.
pub fn try_mixfix_rep_slots_with<E>(
    classify: impl FnOnce() -> Result<Option<InfixRuleInfo>, E>,
) -> Result<Vec<MixfixRepSlot>, CollectionAssemblyError<E>> {
    let Some(info) = classify().map_err(CollectionAssemblyError::Callback)? else {
        return Ok(Vec::new());
    };
    info.mixfix_parts
        .iter()
        .enumerate()
        .filter_map(|(index, part)| {
            part.repetition.as_ref().map(|rep| {
                let slot = u8::try_from(index)
                    .map_err(|_| CollectionAssemblyError::MixfixPartIndex { index })?;
                Ok((
                    slot,
                    part.operand_category.clone(),
                    rep.separator.clone(),
                    rep.close.clone(),
                    rep.min,
                ))
            })
        })
        .collect()
}

/// Discover the original finite map in original rule/slot order.
pub fn try_build_collection_specs<'source, Rule: 'source, C>(
    categories: &[String],
    per_cat: &'source [Vec<Rule>],
    context: &mut C,
) -> Result<Vec<GeneratedCollectionSpecArm>, CollectionAssemblyError<C::Error>>
where
    C: CollectionAssemblyContext<'source, Rule>,
{
    let mut arms = Vec::new();
    let mut indices = BTreeMap::new();
    let mut conflict: Option<String> = None;
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let result_src_idx = u16::try_from(cat_i)
                .map_err(|_| CollectionAssemblyError::CategoryIndex { index: cat_i })?;
            let rule_idx = u16::try_from(rule_i)
                .map_err(|_| CollectionAssemblyError::RuleIndex { index: rule_i })?;
            for (slot_idx, elem_cat, sep, close, min_elements) in
                try_mixfix_rep_slots(rule, context)?
            {
                let close_str = close.first().cloned().unwrap_or_default();
                let spec = GeneratedCollectionSpec {
                    open: String::new(),
                    has_synth_paren: false,
                    close: close_str,
                    sep,
                    min_elements,
                    kv_sep: None,
                    kv_value_optional: false,
                    element_src_idx: try_lookup_element_src_idx(&elem_cat, categories)?,
                    close_resumes_via_unwinding: true,
                };
                if conflict.is_none() {
                    conflict = insert_collection_spec_arm(
                        &mut arms,
                        &mut indices,
                        (result_src_idx, rule_idx, slot_idx),
                        spec,
                        format!(
                            "mixfix repetition in category {cat_i}, rule {rule_i} ({})",
                            context
                                .try_label(rule)
                                .map_err(CollectionAssemblyError::Callback)?
                        ),
                    )
                    .err();
                }
            }
            let Some(shape) = context
                .try_collection(rule)
                .map_err(CollectionAssemblyError::Callback)?
            else {
                if let Some(bshape) = context
                    .try_binder(rule)
                    .map_err(CollectionAssemblyError::Callback)?
                {
                    for info in binder_collection_infos(&bshape) {
                        let slot_idx = info.slot_idx;
                        let spec = GeneratedCollectionSpec {
                            open: String::new(),
                            has_synth_paren: false,
                            close: info.close.clone(),
                            sep: info.separator.clone(),
                            min_elements: 0,
                            kv_sep: info.key_val_separator.clone(),
                            kv_value_optional: false,
                            element_src_idx: try_lookup_element_src_idx(
                                &info.elem_cat,
                                categories,
                            )?,
                            close_resumes_via_unwinding: true,
                        };
                        if conflict.is_none() {
                            conflict = insert_collection_spec_arm(
                                &mut arms,
                                &mut indices,
                                (result_src_idx, rule_idx, slot_idx),
                                spec,
                                format!(
                                    "binder collection in category {cat_i}, rule {rule_i} ({})",
                                    context
                                        .try_label(rule)
                                        .map_err(CollectionAssemblyError::Callback)?
                                ),
                            )
                            .err();
                        }
                    }
                }
                continue;
            };
            let kv_value_optional = matches!(shape.coll_kind, CollectionType::PathMap);
            let spec = GeneratedCollectionSpec {
                open: shape.open_token.clone(),
                has_synth_paren: shape.has_synth_paren,
                close: shape.close.clone(),
                sep: shape.separator.clone(),
                min_elements: 0,
                kv_sep: shape.pair_separator.clone(),
                kv_value_optional,
                element_src_idx: try_lookup_element_src_idx(&shape.element_cat, categories)?,
                close_resumes_via_unwinding: false,
            };
            if conflict.is_none() {
                conflict = insert_collection_spec_arm(
                    &mut arms,
                    &mut indices,
                    (result_src_idx, rule_idx, 0),
                    spec,
                    format!(
                        "collection literal in category {cat_i}, rule {rule_i} ({})",
                        context
                            .try_label(rule)
                            .map_err(CollectionAssemblyError::Callback)?
                    ),
                )
                .err();
            }
        }
    }
    match conflict {
        Some(message) => Err(CollectionAssemblyError::Conflict(message)),
        None => Ok(arms),
    }
}

pub fn try_has_any_collection_slot<'source, Rule: 'source, C>(
    per_cat: &'source [Vec<Rule>],
    context: &mut C,
) -> Result<bool, CollectionAssemblyError<C::Error>>
where
    C: CollectionAssemblyContext<'source, Rule>,
{
    for rules in per_cat {
        for rule in rules {
            if context
                .try_collection(rule)
                .map_err(CollectionAssemblyError::Callback)?
                .is_some()
            {
                return Ok(true);
            }
            if let Some(shape) = context
                .try_binder(rule)
                .map_err(CollectionAssemblyError::Callback)?
            {
                if !binder_collection_infos(&shape).is_empty() {
                    return Ok(true);
                }
            }
            if !try_mixfix_rep_slots(rule, context)?.is_empty() {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn collect_binder_close_delimiters(positions: &[BinderPosition], closes: &mut BTreeSet<String>) {
    let mut work: Vec<&BinderPosition> = positions.iter().rev().collect();
    while let Some(position) = work.pop() {
        match position {
            BinderPosition::BinderListLoop { close, inner_positions, .. } => {
                if !close.is_empty() {
                    closes.insert(close.clone());
                }
                work.extend(inner_positions.iter().rev());
            },
            BinderPosition::ParamParse { collection: Some(info), .. } => {
                if !info.close.is_empty() {
                    closes.insert(info.close.clone());
                }
            },
            BinderPosition::OptionalGroup { positions: inner, .. } => {
                work.extend(inner.iter().rev());
            },
            _ => {},
        }
    }
}

pub fn try_collect_structural_delimiters<'source, Rule: 'source, C>(
    per_cat: &'source [Vec<Rule>],
    context: &mut C,
) -> Result<(BTreeSet<String>, BTreeSet<String>), CollectionAssemblyError<C::Error>>
where
    C: CollectionAssemblyContext<'source, Rule>,
{
    let mut opens = BTreeSet::new();
    let mut closes = BTreeSet::new();
    opens.insert("(".to_string());
    closes.insert(")".to_string());
    for rules in per_cat {
        for rule in rules {
            if let Some(shape) = context
                .try_collection(rule)
                .map_err(CollectionAssemblyError::Callback)?
            {
                opens.insert(shape.open_token);
                if shape.has_synth_paren {
                    opens.insert("(".to_string());
                }
                closes.insert(shape.close);
                continue;
            }
            if let Some(shape) = context
                .try_binder(rule)
                .map_err(CollectionAssemblyError::Callback)?
            {
                collect_binder_close_delimiters(&shape.positions, &mut closes);
            }
        }
    }
    Ok((opens, closes))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_power::{Associativity, MixfixPart, MixfixRep};

    #[derive(Clone, Copy)]
    enum Form {
        Empty,
        Literal,
        RepetitionAndLiteral,
    }
    #[derive(Clone, Copy)]
    struct Rule {
        id: usize,
        form: Form,
    }

    #[derive(Default)]
    struct Context {
        calls: Vec<(&'static str, usize)>,
        fail_at: Option<usize>,
    }
    impl Context {
        fn observe(&mut self, method: &'static str, rule: &Rule) -> Result<(), &'static str> {
            let index = self.calls.len();
            self.calls.push((method, rule.id));
            if self.fail_at == Some(index) {
                Err("denied")
            } else {
                Ok(())
            }
        }
    }

    fn collection(kind: CollectionType) -> CollectionShape<CollectionType> {
        CollectionShape {
            open_token: "{".into(),
            has_synth_paren: false,
            close: "}".into(),
            separator: ",".into(),
            pair_separator: Some(":".into()),
            element_cat: "Term".into(),
            coll_kind: kind,
            label: "Build".into(),
        }
    }

    fn part(repetition: bool) -> MixfixPart {
        MixfixPart {
            operand_category: "Term".into(),
            param_name: "items".into(),
            preceding_terminals: vec![],
            following_terminals: vec![],
            capture_kind: None,
            repetition: repetition.then(|| MixfixRep {
                separator: ";".into(),
                min: 1,
                close: vec![")".into(), "ignored".into()],
            }),
        }
    }

    fn infix(parts: Vec<MixfixPart>) -> InfixRuleInfo {
        InfixRuleInfo {
            label: "Build".into(),
            terminal: "!".into(),
            category: "Term".into(),
            result_category: "Term".into(),
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: true,
            mixfix_parts: parts,
            nullary_literals: vec![],
        }
    }

    impl<'source> CollectionAssemblyContext<'source, Rule> for Context {
        type Error = &'static str;
        type Label = &'static str;
        fn try_infix(&mut self, rule: &'source Rule) -> Result<Option<InfixRuleInfo>, Self::Error> {
            self.observe("infix", rule)?;
            Ok(matches!(rule.form, Form::RepetitionAndLiteral).then(|| infix(vec![part(true)])))
        }
        fn try_collection(
            &mut self,
            rule: &'source Rule,
        ) -> Result<Option<CollectionShape<CollectionType>>, Self::Error> {
            self.observe("collection", rule)?;
            Ok((!matches!(rule.form, Form::Empty)).then(|| collection(CollectionType::PathMap)))
        }
        fn try_binder(&mut self, rule: &'source Rule) -> Result<Option<BinderShape>, Self::Error> {
            self.observe("binder", rule)?;
            Ok(None)
        }
        fn try_label(&mut self, rule: &'source Rule) -> Result<Self::Label, Self::Error> {
            self.observe("label", rule)?;
            Ok("Build")
        }
    }

    #[test]
    fn original_table_fields_and_optional_empty_rows() {
        let per_cat = vec![
            vec![Rule { id: 0, form: Form::Literal }, Rule { id: 1, form: Form::Empty }],
            vec![],
        ];
        let mut context = Context::default();
        let rows =
            try_build_collection_specs(&["Term".into(), "Unused".into()], &per_cat, &mut context)
                .unwrap();
        assert_eq!(
            rows,
            [GeneratedCollectionSpecArm {
                key: (0, 0, 0),
                spec: GeneratedCollectionSpec {
                    open: "{".into(),
                    has_synth_paren: false,
                    close: "}".into(),
                    sep: ",".into(),
                    min_elements: 0,
                    kv_sep: Some(":".into()),
                    kv_value_optional: true,
                    element_src_idx: Some(0),
                    close_resumes_via_unwinding: false,
                },
                first_origin: "collection literal in category 0, rule 0 (Build)".into(),
            }]
        );
        assert_eq!(
            context.calls,
            [
                ("infix", 0),
                ("collection", 0),
                ("label", 0),
                ("infix", 1),
                ("collection", 1),
                ("binder", 1),
            ]
        );
        let empty: Vec<Vec<Rule>> = vec![];
        assert!(try_build_collection_specs(&[], &empty, &mut Context::default())
            .unwrap()
            .is_empty());
    }

    #[test]
    fn collision_skips_later_labels_but_not_remaining_discovery() {
        let per_cat = vec![vec![
            Rule { id: 0, form: Form::RepetitionAndLiteral },
            Rule { id: 1, form: Form::Empty },
            Rule { id: 2, form: Form::Literal },
        ]];
        let mut context = Context::default();
        let result = try_build_collection_specs(&["Term".into()], &per_cat, &mut context);
        let Err(CollectionAssemblyError::Conflict(message)) = result else {
            panic!("expected collision");
        };
        assert!(message.contains("mixfix repetition in category 0, rule 0 (Build)"));
        assert!(message.contains("collection literal in category 0, rule 0 (Build)"));
        assert_eq!(
            context.calls,
            [
                ("infix", 0),
                ("label", 0),
                ("collection", 0),
                ("label", 0),
                ("infix", 1),
                ("collection", 1),
                ("binder", 1),
                ("infix", 2),
                ("collection", 2),
            ]
        );
        for failure in 0..context.calls.len() {
            let mut refused = Context {
                fail_at: Some(failure),
                ..Context::default()
            };
            assert_eq!(
                try_build_collection_specs(&["Term".into()], &per_cat, &mut refused),
                Err(CollectionAssemblyError::Callback("denied")),
            );
            assert_eq!(refused.calls, context.calls[..=failure]);
        }
    }

    #[test]
    fn equal_discovery_retains_first_origin_and_conflict_does_not_mutate() {
        let spec = GeneratedCollectionSpec {
            open: "".into(),
            has_synth_paren: false,
            close: ")".into(),
            sep: ",".into(),
            min_elements: 0,
            kv_sep: None,
            kv_value_optional: false,
            element_src_idx: None,
            close_resumes_via_unwinding: true,
        };
        let mut arms = vec![];
        let mut indices = BTreeMap::new();
        insert_collection_spec_arm(
            &mut arms,
            &mut indices,
            (2, 3, 4),
            spec.clone(),
            "first".into(),
        )
        .unwrap();
        insert_collection_spec_arm(&mut arms, &mut indices, (2, 3, 4), spec.clone(), "same".into())
            .unwrap();
        assert_eq!(arms.len(), 1);
        assert_eq!(arms[0].first_origin, "first");
        let before = arms.clone();
        let mut other = spec;
        other.close = "]".into();
        assert!(insert_collection_spec_arm(
            &mut arms,
            &mut indices,
            (2, 3, 4),
            other,
            "second".into()
        )
        .is_err());
        assert_eq!(arms, before);
    }

    #[test]
    fn selected_repetition_part_is_checked_not_total_part_count() {
        let mut parts = vec![part(false); 257];
        parts[255] = part(true);
        let slots = try_mixfix_rep_slots_with::<()>(|| Ok(Some(infix(parts.clone())))).unwrap();
        assert_eq!(
            slots,
            [(255, "Term".into(), ";".into(), vec![")".into(), "ignored".into()], 1)]
        );
        parts[256] = part(true);
        assert_eq!(
            try_mixfix_rep_slots_with::<()>(|| Ok(Some(infix(parts)))),
            Err(CollectionAssemblyError::MixfixPartIndex { index: 256 }),
        );
    }

    #[test]
    fn first_element_lookup_preserves_absence_duplicates_and_width() {
        let mut categories = vec![String::new(); 65537];
        categories[65535] = "Term".into();
        categories[65536] = "Term".into();
        assert_eq!(try_lookup_element_src_idx::<()>("Missing", &categories), Ok(None));
        assert_eq!(try_lookup_element_src_idx::<()>("Term", &categories), Ok(Some(65535)));
        categories[65535].clear();
        assert_eq!(
            try_lookup_element_src_idx::<()>("Term", &categories),
            Err(CollectionAssemblyError::ElementCategoryIndex { index: 65536 })
        );
    }

    #[test]
    fn category_and_rule_widths_are_checked_when_original_cast_is_reached() {
        let mut categories: Vec<Vec<Rule>> = vec![vec![]; 65537];
        assert!(try_build_collection_specs(&[], &categories, &mut Context::default())
            .unwrap()
            .is_empty());
        categories[65536].push(Rule { id: 0, form: Form::Empty });
        let mut context = Context::default();
        assert_eq!(
            try_build_collection_specs(&[], &categories, &mut context),
            Err(CollectionAssemblyError::CategoryIndex { index: 65536 })
        );
        assert!(context.calls.is_empty());

        let rules = vec![vec![Rule { id: 0, form: Form::Empty }; 65537]];
        assert_eq!(
            try_build_collection_specs(&[], &rules, &mut Context::default()),
            Err(CollectionAssemblyError::RuleIndex { index: 65536 })
        );
    }

    #[test]
    fn existence_and_delimiter_workers_retain_distinct_original_probe_order() {
        let rules = vec![vec![
            Rule { id: 0, form: Form::Empty },
            Rule { id: 1, form: Form::Literal },
            Rule { id: 2, form: Form::Empty },
        ]];
        let mut context = Context::default();
        assert!(try_has_any_collection_slot(&rules, &mut context).unwrap());
        assert_eq!(
            context.calls,
            [("collection", 0), ("binder", 0), ("infix", 0), ("collection", 1)]
        );
        let mut delimiters = Context::default();
        let (opens, closes) = try_collect_structural_delimiters(&rules, &mut delimiters).unwrap();
        assert_eq!(opens, BTreeSet::from(["(".into(), "{".into()]));
        assert_eq!(closes, BTreeSet::from([")".into(), "}".into()]));
        assert_eq!(
            delimiters.calls,
            [
                ("collection", 0),
                ("binder", 0),
                ("collection", 1),
                ("collection", 2),
                ("binder", 2),
            ]
        );
    }
}
