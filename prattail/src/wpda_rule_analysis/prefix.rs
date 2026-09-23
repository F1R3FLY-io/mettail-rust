//! Original FIRST, unified prefix bucket, and initiating-row derivation.
//!
//! Token quotation stays in the macro adapter. These helpers retain the original
//! FIFO/visited traversal, formatter-key ordering, first payload, duplicate
//! descriptors, lazy factoring observations, and existing fork-emission
//! accumulator. They do not select parse candidates.
//!
//! `UnifiedPrefixDescriptorProjection.v` verifies this relocation boundary and
//! finite call sequences. Callers still supply the original static positions;
//! allocation and arbitrary formatter/reader lawfulness remain caller obligations.
//! `OriginalFirstSetProjection.v` covers the FIRST source-observation boundary,
//! not semantic FIRST completeness or native-helper correctness.

use super::fork_emission::ForkEmissionOrdinalModel;
use std::collections::BTreeMap;

use super::atomic::AtomicDescriptor;
use super::binder::optional::{BinderSyntaxObservation, BinderSyntaxReader};
use super::binder::rule::BinderRuleReader;
use mettail_ast::grammar::NonTerminalKind;

/// Original FIRST row; token quotation belongs to the caller, not this worker.
#[derive(Debug, Clone)]
pub struct FirstToken<P> {
    pub pattern: P,
    pub extra_guard: Option<P>,
    /// Original raw leading structural trigger, retained through deduplication.
    /// Consumers use it to distinguish a direct structural-literal trigger from
    /// a delegated category reading; non-Fixed rows carry no leading literal.
    pub leading_literal: Option<String>,
    /// True only for the original explicit or synthetic variable contribution.
    /// Named Ident captures are authored literal syntax, not variable readings.
    pub is_var_contribution: bool,
}

/// The eight ORIGINAL quotation construction sites, not semantic token equality.
pub enum FirstPredicate<'text> {
    Fixed(&'text str),
    Ident,
    Integer,
    Boolean,
    String,
    Float,
    CaptureName(&'text str),
    GuestOpen(&'text str),
}

/// First legacy item, preserving its existing discriminant and borrowed name.
pub enum FirstLegacyItem<'source, N> {
    Terminal(&'source str),
    NonTerminal { kind: NonTerminalKind, name: N },
    Other,
}

/// Source context for the original FIRST loop, alongside the existing rule reader.
///
/// Rule/declaration order and first-match lookup are authored order. A declaration
/// handle preserves its original role and collection opener, not facts inferred
/// from normalized rules. Native/patterned/binder callbacks execute the existing
/// helpers lazily; `native_first` includes the original native-presence gate and
/// uses the original FirstSet context. No helper is re-derived here.
///
/// The reader/context must describe the same immutable source. `rule_at` is valid
/// exactly below `rules_len`. Pattern rendering must preserve the original pair
/// of formatter keys: semantic-token equality is NOT a substitute. These laws
/// are caller obligations, modeled at the source adapter boundary in
/// `OriginalFirstSetProjection.v`; arbitrary context implementations are not
/// certified by that source-refinement proof.
pub trait FirstSetContext<'source, R: BinderRuleReader<'source>> {
    type Category: Copy;
    type Literal;
    type Pattern: ToString;

    fn rules_len(&self) -> usize;
    fn rule_at(&self, index: usize) -> R::Rule;
    fn find_category(&mut self, name: &str) -> Option<Self::Category>;
    fn is_data(&self, category: Self::Category) -> bool;
    fn collection_open(&self, category: Self::Category) -> Option<&'source str>;
    fn legacy_first(
        &self,
        rule: R::Rule,
    ) -> Option<FirstLegacyItem<'source, <R as BinderSyntaxReader<'source>>::Name>>;
    fn native_first(
        &mut self,
        category: Self::Category,
        name: &str,
    ) -> Vec<(Self::Pattern, Option<Self::Pattern>)>;
    fn atomic(&mut self, rule: R::Rule) -> AtomicDescriptor<Self::Literal>;
    fn patterned_first(
        &mut self,
        literal: Self::Literal,
    ) -> Vec<(Self::Pattern, Option<Self::Pattern>)>;
    fn binder_leading(&mut self, rule: R::Rule) -> Option<String>;
    fn predicate_parts(
        &mut self,
        predicate: FirstPredicate<'_>,
    ) -> (Self::Pattern, Option<Self::Pattern>);
}

/// Additional authored observations used by the original identifier summaries.
/// Declaration order is unchanged; `legacy_at(rule, 0)` must agree with
/// `legacy_first(rule)`. Every position below `legacy_len` must be present,
/// including unsupported items represented by `Other`. Category spelling uses
/// the original formatter, not identifier equality or a reconstructed category.
/// `OriginalIdentSummaryProjection.v` covers this source-substitution boundary;
/// it does not certify the summaries as complete semantic FIRST predicates.
pub trait IdentSummaryContext<'source, R: BinderRuleReader<'source>>:
    FirstSetContext<'source, R>
{
    fn categories_len(&self) -> usize;
    fn category_at(&self, index: usize) -> Self::Category;
    fn category_spelling(&self, category: Self::Category) -> String;
    fn legacy_len(&self, rule: R::Rule) -> usize;
    fn legacy_at(
        &self,
        rule: R::Rule,
        index: usize,
    ) -> Option<FirstLegacyItem<'source, <R as BinderSyntaxReader<'source>>::Name>>;
}

/// Original declaration-first home-variable predicate. An explicit first Var
/// short-circuits the data-role read; undeclared categories refuse immediately.
pub fn result_has_home_var_reading<'source, R, C>(
    cat_name: &str,
    reader: &R,
    context: &mut C,
) -> bool
where
    R: BinderRuleReader<'source>,
    C: FirstSetContext<'source, R>,
{
    let Some(lang_type) = context.find_category(cat_name) else {
        return false;
    };
    let has_user_var = (0..context.rules_len()).any(|index| {
        let rule = context.rule_at(index);
        reader.category(rule).to_string() == cat_name
            && context
                .legacy_first(rule)
                .map(|item| {
                    matches!(item, FirstLegacyItem::NonTerminal { kind: NonTerminalKind::Var, .. })
                })
                .unwrap_or(false)
    });
    has_user_var || !context.is_data(lang_type)
}

/// Original identifier closure: authored rule order, duplicate reverse edges,
/// guard-before-format short-circuit, and HashSet seed enumeration are retained.
pub fn ident_first_categories<'source, R, C>(
    reader: &R,
    context: &mut C,
) -> std::collections::HashSet<String>
where
    R: BinderRuleReader<'source>,
    C: IdentSummaryContext<'source, R>,
{
    let mut reached: std::collections::HashSet<String> = (0..context.categories_len())
        .map(|index| context.category_at(index))
        .filter(|ty| !context.is_data(*ty))
        .map(|ty| context.category_spelling(ty))
        .collect();
    let mut reverse: std::collections::HashMap<String, Vec<String>> =
        std::collections::HashMap::new();

    for index in 0..context.rules_len() {
        let rule = context.rule_at(index);
        let category = reader.category(rule).to_string();
        match context.atomic(rule) {
            AtomicDescriptor::VarRule { .. } => {
                reached.insert(category);
            },
            AtomicDescriptor::LiteralPatterned(literal) => {
                let has_ident =
                    context
                        .patterned_first(literal)
                        .into_iter()
                        .any(|(pattern, guard)| {
                            guard.is_none() && pattern.to_string().contains("Ident")
                        });
                if has_ident {
                    reached.insert(category);
                }
            },
            AtomicDescriptor::CrossCatProjection { source_cat_name, .. } => {
                reverse.entry(source_cat_name).or_default().push(category);
            },
            AtomicDescriptor::NonAtomic => {
                if matches!(
                    reader
                        .syntax_pattern(rule)
                        .and_then(|pattern| reader.at(pattern, 0)),
                    Some(BinderSyntaxObservation::Param(_))
                ) {
                    if let Some(FirstLegacyItem::NonTerminal {
                        name,
                        kind: NonTerminalKind::Category,
                    }) = context.legacy_first(rule)
                    {
                        let source = name.to_string();
                        if source != category {
                            reverse.entry(source).or_default().push(category);
                        }
                    }
                }
            },
            AtomicDescriptor::TerminalKeyword { .. }
            | AtomicDescriptor::LiteralInteger
            | AtomicDescriptor::LiteralBoolean
            | AtomicDescriptor::LiteralString
            | AtomicDescriptor::LiteralFloat
            | AtomicDescriptor::CrossCatPrefixUnary { .. }
            | AtomicDescriptor::PrefixOperator { .. }
            | AtomicDescriptor::NullaryLiteralRun { .. } => {},
        }
    }

    let mut pending: std::collections::VecDeque<_> = reached.iter().cloned().collect();
    while let Some(source) = pending.pop_front() {
        if let Some(targets) = reverse.get(&source) {
            for target in targets {
                if reached.insert(target.clone()) {
                    pending.push_back(target.clone());
                }
            }
        }
    }
    reached
}

/// Original explicit-frame var-only traversal, not a new FIRST recognizer.
/// The closure is eager; each cursor advances before the rule is inspected.
/// Purity retains its three separate, short-circuiting source passes.
pub fn source_ident_first_is_var_only<'source, R, C>(
    source_cat: &str,
    reader: &R,
    context: &mut C,
) -> bool
where
    R: BinderRuleReader<'source>,
    C: IdentSummaryContext<'source, R>,
{
    struct Frame {
        category: String,
        next_rule: usize,
    }

    let ident_first = ident_first_categories(reader, context);
    let mut rules_by_category: std::collections::HashMap<String, Vec<R::Rule>> =
        std::collections::HashMap::new();
    for index in 0..context.rules_len() {
        let rule = context.rule_at(index);
        rules_by_category
            .entry(reader.category(rule).to_string())
            .or_default()
            .push(rule);
    }

    let mut visited = std::collections::HashSet::from([source_cat.to_string()]);
    let mut frames = vec![Frame {
        category: source_cat.to_string(),
        next_rule: 0,
    }];
    while let Some(frame) = frames.last_mut() {
        let rules = rules_by_category
            .get(&frame.category)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let Some(rule) = rules.get(frame.next_rule).copied() else {
            frames.pop();
            continue;
        };
        frame.next_rule += 1;

        let is_var_rule = context
            .legacy_first(rule)
            .map(|item| {
                matches!(item, FirstLegacyItem::NonTerminal { kind: NonTerminalKind::Var, .. })
            })
            .unwrap_or(false);
        if is_var_rule {
            continue;
        }
        match context.legacy_first(rule) {
            Some(FirstLegacyItem::Terminal(_)) => continue,
            Some(FirstLegacyItem::NonTerminal { name, kind: NonTerminalKind::Category }) => {
                let nt_cat = name.to_string();
                if nt_cat == frame.category {
                    continue;
                }
                let structural_item_count = (0..context.legacy_len(rule))
                    .filter(|index| {
                        !matches!(
                            context.legacy_at(rule, *index),
                            Some(FirstLegacyItem::Terminal(_))
                        )
                    })
                    .count();
                let is_pure_projection = structural_item_count == 1
                    && (0..context.legacy_len(rule)).all(|index| {
                        matches!(
                            context.legacy_at(rule, index),
                            Some(
                                FirstLegacyItem::NonTerminal {
                                    kind: NonTerminalKind::Category,
                                    ..
                                } | FirstLegacyItem::Terminal(_)
                            )
                        )
                    })
                    && (0..context.legacy_len(rule)).all(|index| {
                        !matches!(
                            context.legacy_at(rule, index),
                            Some(FirstLegacyItem::Terminal(_))
                        )
                    });
                if ident_first.contains(&nt_cat) {
                    if is_pure_projection && !visited.insert(nt_cat.clone()) {
                        continue;
                    }
                    if is_pure_projection {
                        frames.push(Frame { category: nt_cat, next_rule: 0 });
                        continue;
                    }
                    return false;
                }
                continue;
            },
            Some(FirstLegacyItem::NonTerminal { kind: NonTerminalKind::Var, .. }) => continue,
            _ => {
                if let Some(sp) = reader.syntax_pattern(rule) {
                    match reader.at(sp, 0) {
                        Some(BinderSyntaxObservation::Literal(_)) => continue,
                        Some(BinderSyntaxObservation::Param(_)) => return false,
                        _ => return false,
                    }
                } else {
                    return false;
                }
            },
        }
    }
    true
}

impl<P> FirstToken<P> {
    fn fixed_leading(sigil: &str, pattern: P, extra_guard: Option<P>) -> Self {
        Self {
            pattern,
            extra_guard,
            leading_literal: Some(sigil.to_string()),
            is_var_contribution: false,
        }
    }
}

/// Original direct leading-literal set. Present empty/nonliteral syntax suppresses
/// legacy fallback; only absent syntax consults the first legacy Terminal.
pub fn category_leading_literals<'source, R, C>(
    cat_name: &str,
    reader: &R,
    context: &C,
) -> std::collections::BTreeSet<String>
where
    R: BinderRuleReader<'source>,
    C: FirstSetContext<'source, R>,
{
    let mut out = std::collections::BTreeSet::new();
    for index in 0..context.rules_len() {
        let rule = context.rule_at(index);
        if reader.category(rule).to_string() != cat_name {
            continue;
        }
        if let Some(sp) = reader.syntax_pattern(rule) {
            if let Some(BinderSyntaxObservation::Literal(text)) = reader.at(sp, 0) {
                out.insert(text.to_string());
            }
        } else if let Some(FirstLegacyItem::Terminal(text)) = context.legacy_first(rule) {
            out.insert(text.to_string());
        }
    }
    out
}

/// Original FIFO FIRST traversal and stable formatter-key deduplication.
/// The complete first row survives, including metadata and guard Option.
pub fn first_set_of_category<'source, R, C>(
    cat_name: &str,
    reader: &R,
    context: &mut C,
) -> Vec<FirstToken<C::Pattern>>
where
    R: BinderRuleReader<'source>,
    C: FirstSetContext<'source, R>,
{
    let mut acc = Vec::new();
    let mut visited = std::collections::HashSet::new();
    collect_first_set(cat_name, reader, context, &mut acc, &mut visited);
    let mut seen: std::collections::BTreeSet<(String, String)> = std::collections::BTreeSet::new();
    acc.retain(|ft| {
        let key = (
            ft.pattern.to_string(),
            ft.extra_guard
                .as_ref()
                .map(|g| g.to_string())
                .unwrap_or_default(),
        );
        seen.insert(key)
    });
    acc
}

fn collect_first_set<'source, R, C>(
    cat_name: &str,
    reader: &R,
    context: &mut C,
    acc: &mut Vec<FirstToken<C::Pattern>>,
    visited: &mut std::collections::HashSet<String>,
) where
    R: BinderRuleReader<'source>,
    C: FirstSetContext<'source, R>,
{
    let mut pending = std::collections::VecDeque::new();
    pending.push_back(cat_name.to_string());

    while let Some(current_cat_name) = pending.pop_front() {
        if !visited.insert(current_cat_name.clone()) {
            continue;
        }
        if let Some(lang_type) = context.find_category(&current_cat_name) {
            for (pattern, extra_guard) in context.native_first(lang_type, &current_cat_name) {
                acc.push(FirstToken {
                    pattern,
                    extra_guard,
                    leading_literal: None,
                    is_var_contribution: false,
                });
            }
        }
        if let Some(lang_type) = context.find_category(&current_cat_name) {
            if !context.is_data(lang_type) {
                let has_user_var = (0..context.rules_len()).any(|index| {
                    let rule = context.rule_at(index);
                    reader.category(rule).to_string() == current_cat_name
                        && matches!(
                            context.legacy_first(rule),
                            Some(FirstLegacyItem::NonTerminal { kind: NonTerminalKind::Var, .. })
                        )
                });
                if !has_user_var {
                    let (pattern, extra_guard) = context.predicate_parts(FirstPredicate::Ident);
                    acc.push(FirstToken {
                        pattern,
                        extra_guard,
                        leading_literal: None,
                        is_var_contribution: true,
                    });
                }
            }
        }
        if let Some(lang_type) = context.find_category(&current_cat_name) {
            if let Some(open) = context.collection_open(lang_type) {
                let first_open = open.trim_end_matches('(').to_string();
                let (pattern, extra_guard) =
                    context.predicate_parts(FirstPredicate::Fixed(&first_open));
                acc.push(FirstToken::fixed_leading(&first_open, pattern, extra_guard));
            }
        }
        for index in 0..context.rules_len() {
            let rule = context.rule_at(index);
            if reader.category(rule).to_string() != current_cat_name {
                continue;
            }
            let shape = context.atomic(rule);
            match shape {
                AtomicDescriptor::LiteralPatterned(literal) => {
                    for (pattern, extra_guard) in context.patterned_first(literal) {
                        acc.push(FirstToken {
                            pattern,
                            extra_guard,
                            leading_literal: None,
                            is_var_contribution: false,
                        });
                    }
                },
                AtomicDescriptor::TerminalKeyword { terminal_text, .. } => {
                    let (pattern, extra_guard) =
                        context.predicate_parts(FirstPredicate::Fixed(&terminal_text));
                    acc.push(FirstToken::fixed_leading(&terminal_text, pattern, extra_guard));
                },
                AtomicDescriptor::VarRule { .. } => {
                    let (pattern, extra_guard) = context.predicate_parts(FirstPredicate::Ident);
                    acc.push(FirstToken {
                        pattern,
                        extra_guard,
                        leading_literal: None,
                        is_var_contribution: true,
                    });
                },
                AtomicDescriptor::LiteralInteger => {
                    let (pattern, extra_guard) = context.predicate_parts(FirstPredicate::Integer);
                    acc.push(FirstToken {
                        pattern,
                        extra_guard,
                        leading_literal: None,
                        is_var_contribution: false,
                    });
                },
                AtomicDescriptor::LiteralBoolean => {
                    let (pattern, extra_guard) = context.predicate_parts(FirstPredicate::Boolean);
                    acc.push(FirstToken {
                        pattern,
                        extra_guard,
                        leading_literal: None,
                        is_var_contribution: false,
                    });
                },
                AtomicDescriptor::LiteralString => {
                    let (pattern, extra_guard) = context.predicate_parts(FirstPredicate::String);
                    acc.push(FirstToken {
                        pattern,
                        extra_guard,
                        leading_literal: None,
                        is_var_contribution: false,
                    });
                },
                AtomicDescriptor::LiteralFloat => {
                    let (pattern, extra_guard) = context.predicate_parts(FirstPredicate::Float);
                    acc.push(FirstToken {
                        pattern,
                        extra_guard,
                        leading_literal: None,
                        is_var_contribution: false,
                    });
                },
                AtomicDescriptor::CrossCatProjection { source_cat_name, .. } => {
                    pending.push_back(source_cat_name);
                },
                AtomicDescriptor::CrossCatPrefixUnary { trigger, .. } => {
                    let (pattern, extra_guard) =
                        context.predicate_parts(FirstPredicate::Fixed(&trigger));
                    acc.push(FirstToken::fixed_leading(&trigger, pattern, extra_guard));
                },
                AtomicDescriptor::PrefixOperator { trigger, .. } => {
                    let (pattern, extra_guard) =
                        context.predicate_parts(FirstPredicate::Fixed(&trigger));
                    acc.push(FirstToken::fixed_leading(&trigger, pattern, extra_guard));
                },
                AtomicDescriptor::NullaryLiteralRun { trigger, .. } => {
                    let (pattern, extra_guard) =
                        context.predicate_parts(FirstPredicate::Fixed(&trigger));
                    acc.push(FirstToken::fixed_leading(&trigger, pattern, extra_guard));
                },
                AtomicDescriptor::NonAtomic => {
                    if let Some(sp) = reader.syntax_pattern(rule) {
                        match reader.at(sp, 0) {
                            Some(BinderSyntaxObservation::Literal(text)) => {
                                let (pattern, extra_guard) =
                                    context.predicate_parts(FirstPredicate::Fixed(text));
                                acc.push(FirstToken::fixed_leading(text, pattern, extra_guard));
                            },
                            Some(BinderSyntaxObservation::Param(_)) => {
                                let leading_cat = context.binder_leading(rule).or_else(|| {
                                    match context.legacy_first(rule) {
                                        Some(FirstLegacyItem::NonTerminal {
                                            name,
                                            kind: NonTerminalKind::Category,
                                        }) => Some(name.to_string()),
                                        _ => None,
                                    }
                                });
                                if let Some(nt_cat) = leading_cat {
                                    if nt_cat != current_cat_name {
                                        pending.push_back(nt_cat);
                                    }
                                }
                            },
                            Some(BinderSyntaxObservation::TokenKind { name, .. }) => {
                                let kind_name = name.to_string();
                                let (pattern, extra_guard) = context
                                    .predicate_parts(FirstPredicate::CaptureName(&kind_name));
                                acc.push(FirstToken {
                                    pattern,
                                    extra_guard,
                                    leading_literal: None,
                                    is_var_contribution: false,
                                });
                            },
                            Some(BinderSyntaxObservation::GuestBody { open, .. }) => {
                                let open_kind = open.to_string();
                                let (pattern, extra_guard) =
                                    context.predicate_parts(FirstPredicate::GuestOpen(&open_kind));
                                acc.push(FirstToken {
                                    pattern,
                                    extra_guard,
                                    leading_literal: None,
                                    is_var_contribution: false,
                                });
                            },
                            _ => {},
                        }
                    }
                },
            }
        }
    }
}

/// One original unified dispatch bucket, independent of token quotation.
pub struct UnifiedBucket<P, D> {
    pub pat: P,
    pub extra_guard: Option<P>,
    pub descs: Vec<D>,
}

/// Insert exactly as the original macro helper: first-key order, first payload,
/// and every incoming descriptor. An absent guard and an empty-rendering guard
/// have the same key but retain the first guard's original Option payload.
pub fn insert_unified_descriptor<P: ToString, D>(
    unified_buckets: &mut BTreeMap<(String, String), UnifiedBucket<P, D>>,
    unified_order: &mut Vec<(String, String)>,
    pattern: P,
    extra_guard: Option<P>,
    desc: D,
) {
    let pat_str = pattern.to_string();
    let guard_str = extra_guard
        .as_ref()
        .map(|g| g.to_string())
        .unwrap_or_default();
    let key = (pat_str, guard_str);
    if !unified_buckets.contains_key(&key) {
        unified_order.push(key.clone());
    }
    let entry = unified_buckets.entry(key).or_insert_with(|| UnifiedBucket {
        pat: pattern,
        extra_guard,
        descs: Vec::new(),
    });
    entry.descs.push(desc);
}

/// Only the existing factoring tags read by initiating-row recording.
/// The three GroupFirst payload indices remain with the factoring consumer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InitiatingRuleDisposition {
    GroupFirst,
    GroupRest,
}

/// The original missing-members refusal, before any rows from this call are
/// recorded. Earlier calls' accumulated rows remain untouched.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MissingInitiatingRuleMembers {
    pub category_src_idx: u16,
    pub rule_idx: u16,
}

/// Record the original initiating rows using the existing shared accumulator.
/// Member lookup occurs only for GroupFirst; members retain order and duplicates.
/// GroupRest does not renumber any static positions supplied by the caller.
#[allow(clippy::too_many_arguments)]
#[must_use]
pub fn record_initiating_rule_rows<'members>(
    fork_rows: &mut ForkEmissionOrdinalModel,
    category_src_idx: u16,
    rule_idx: u16,
    branch_position: u16,
    disposition: impl FnOnce(u16) -> Option<InitiatingRuleDisposition>,
    group_members: impl FnOnce(u16) -> Option<&'members [u16]>,
    bucket_tag: &str,
) -> Option<MissingInitiatingRuleMembers> {
    match disposition(rule_idx) {
        Some(InitiatingRuleDisposition::GroupFirst) => {
            let Some(members) = group_members(rule_idx) else {
                return Some(MissingInitiatingRuleMembers { category_src_idx, rule_idx });
            };
            for &member in members {
                fork_rows.record_site2_row(category_src_idx, member, branch_position, bucket_tag);
            }
            None
        },
        Some(InitiatingRuleDisposition::GroupRest) => None,
        None => {
            fork_rows.record_site2_row(category_src_idx, rule_idx, branch_position, bucket_tag);
            None
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    #[test]
    fn first_owned_handles_preserve_lookup_order_and_first_complete_payload() {
        use crate::wpda_rule_analysis::authored::{AuthoredNameRef, AuthoredRuleReader};
        use mettail_grammar_core::{
            AuthoredName, AuthoredNameId, AuthoredNode, AuthoredRule, AuthoredRuleId,
            AuthoredRuleStore, AuthoredSyntax, AuthoredSyntaxId,
        };

        struct Payload {
            key: String,
            origin: u32,
        }
        impl std::fmt::Display for Payload {
            fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                output.write_str(&self.key)
            }
        }
        struct Context {
            rule: AuthoredRuleId,
            events: RefCell<Vec<String>>,
        }
        impl<'source> FirstSetContext<'source, AuthoredRuleReader<'source>> for Context {
            type Category = ();
            type Literal = ();
            type Pattern = Payload;
            fn rules_len(&self) -> usize {
                1
            }
            fn rule_at(&self, index: usize) -> AuthoredRuleId {
                assert_eq!(index, 0);
                self.rule
            }
            fn find_category(&mut self, name: &str) -> Option<()> {
                assert_eq!(name, "A");
                self.events.borrow_mut().push("find".into());
                Some(())
            }
            fn is_data(&self, _: ()) -> bool {
                self.events.borrow_mut().push("data".into());
                true
            }
            fn collection_open(&self, _: ()) -> Option<&'source str> {
                self.events.borrow_mut().push("collection".into());
                Some("open((")
            }
            fn legacy_first(
                &self,
                _: AuthoredRuleId,
            ) -> Option<FirstLegacyItem<'source, AuthoredNameRef<'source>>> {
                panic!("present literal syntax and data role must not query legacy fallback")
            }
            fn native_first(&mut self, _: (), _: &str) -> Vec<(Payload, Option<Payload>)> {
                self.events.borrow_mut().push("native".into());
                vec![(Payload { key: "dup".into(), origin: 1 }, None)]
            }
            fn atomic(&mut self, rule: AuthoredRuleId) -> AtomicDescriptor<()> {
                assert_eq!(rule, self.rule);
                self.events.borrow_mut().push("atomic".into());
                AtomicDescriptor::NonAtomic
            }
            fn patterned_first(&mut self, _: ()) -> Vec<(Payload, Option<Payload>)> {
                panic!("non-atomic fixture must not expand patterned literals")
            }
            fn binder_leading(&mut self, _: AuthoredRuleId) -> Option<String> {
                panic!("literal first syntax must not classify a binder")
            }
            fn predicate_parts(
                &mut self,
                predicate: FirstPredicate<'_>,
            ) -> (Payload, Option<Payload>) {
                let FirstPredicate::Fixed(text) = predicate else {
                    panic!("fixture contributes fixed tokens only");
                };
                self.events.borrow_mut().push(format!("quote:{text}"));
                (
                    Payload { key: text.into(), origin: 2 },
                    Some(Payload { key: String::new(), origin: 3 }),
                )
            }
        }

        let mut store = AuthoredRuleStore::new();
        let name = AuthoredNameId(
            store
                .try_push(AuthoredNode::Name(AuthoredName {
                    spelling: "A".into(),
                    equality_class: 0,
                }))
                .expect("first authored name"),
        );
        let syntax = AuthoredSyntaxId(
            store
                .try_push(AuthoredNode::Syntax(vec![AuthoredSyntax::Literal("dup".into())]))
                .expect("owned literal syntax"),
        );
        let rule = AuthoredRuleId(
            store
                .try_push(AuthoredNode::Rule(AuthoredRule {
                    label: name,
                    category: name,
                    term_context: None,
                    syntax_pattern: Some(syntax),
                    items: Vec::new(),
                }))
                .expect("backward authored rule references"),
        );
        let reader = AuthoredRuleReader::new(&store).expect("representable owned FIRST source");
        let mut context = Context { rule, events: RefCell::new(Vec::new()) };
        assert_eq!(
            category_leading_literals("A", &reader, &context),
            ["dup".into()].into_iter().collect()
        );
        let output = first_set_of_category("A", &reader, &mut context);
        assert_eq!(output.len(), 2);
        assert_eq!(output[0].pattern.key, "dup");
        assert_eq!(output[0].pattern.origin, 1);
        assert!(output[0].extra_guard.is_none());
        assert!(output[0].leading_literal.is_none());
        assert!(!output[0].is_var_contribution);
        assert_eq!(output[1].pattern.key, "open");
        assert_eq!(output[1].leading_literal.as_deref(), Some("open"));
        assert_eq!(
            context.events.into_inner(),
            [
                "find",
                "native",
                "find",
                "data",
                "find",
                "collection",
                "quote:open",
                "atomic",
                "quote:dup",
            ]
        );
    }

    #[test]
    fn owned_payloads_keep_first_allocation_guard_and_insertion_order() {
        let mut buckets = BTreeMap::new();
        let mut order = Vec::new();
        let first = String::from("z");
        let first_allocation = first.as_ptr();
        insert_unified_descriptor(&mut buckets, &mut order, first, Some(String::new()), 8);
        insert_unified_descriptor(&mut buckets, &mut order, String::from("a"), None, 9);
        insert_unified_descriptor(&mut buckets, &mut order, String::from("z"), None, 8);
        assert_eq!(
            order,
            vec![(String::from("z"), String::new()), (String::from("a"), String::new())]
        );
        let bucket = buckets
            .get(&(String::from("z"), String::new()))
            .expect("first bucket");
        assert_eq!(bucket.pat.as_ptr(), first_allocation);
        assert_eq!(bucket.extra_guard, Some(String::new()));
        assert_eq!(bucket.descs, vec![8, 8]);
        assert_eq!(buckets.keys().map(|key| key.0.as_str()).collect::<Vec<_>>(), vec!["a", "z"]);
    }

    #[test]
    fn group_rest_and_ordinary_rule_never_read_members() {
        for disposition in [Some(InitiatingRuleDisposition::GroupRest), None] {
            let calls = RefCell::new(Vec::new());
            let mut rows = ForkEmissionOrdinalModel::new();
            let error = record_initiating_rule_rows(
                &mut rows,
                u16::MAX,
                4,
                u16::MAX,
                |rule| {
                    calls.borrow_mut().push(rule);
                    disposition
                },
                |_| panic!("members lookup must stay lazy"),
                "static-position",
            );
            assert_eq!(error, None);
            assert_eq!(*calls.borrow(), vec![4]);
            assert_eq!(rows.site2_ordinal(u16::MAX, 4), disposition.is_none().then_some(u16::MAX));
            assert_eq!(rows.site2_row_count(), usize::from(disposition.is_none()));
        }
    }

    #[test]
    fn group_first_reads_in_order_and_preserves_duplicate_accumulator_observations() {
        let calls = RefCell::new(Vec::new());
        let members = [8, 7, 8, 8];
        let mut rows = ForkEmissionOrdinalModel::new();
        rows.record_site2_row(2, 8, 1, "seed");
        let error = record_initiating_rule_rows(
            &mut rows,
            2,
            3,
            6,
            |rule| {
                calls.borrow_mut().push(("disposition", rule));
                Some(InitiatingRuleDisposition::GroupFirst)
            },
            |rule| {
                calls.borrow_mut().push(("members", rule));
                Some(&members)
            },
            "group",
        );
        assert_eq!(error, None);
        assert_eq!(*calls.borrow(), vec![("disposition", 3), ("members", 3)]);
        let (derived, ambiguous) = rows.into_parts();
        assert_eq!(derived.len(), 1);
        let member = derived.get(&(2, 7)).expect("one derived member");
        assert_eq!(member.emission_ordinal, 6);
        assert_eq!(member.bucket_tag, "group");
        assert_eq!(ambiguous.len(), 1);
        assert_eq!(
            ambiguous.get(&(2, 8)).expect("duplicate member history"),
            &vec![
                String::from("seed@1"),
                String::from("group@6"),
                String::from("group@6"),
                String::from("group@6")
            ]
        );
    }

    #[test]
    fn missing_and_empty_members_preserve_prefix_but_have_distinct_outcomes() {
        for members in [None, Some(&[][..])] {
            let calls = RefCell::new(Vec::new());
            let mut rows = ForkEmissionOrdinalModel::new();
            rows.record_site2_row(1, 2, 3, "first");
            rows.record_site2_row(1, 2, 4, "conflicting");
            let before = format!("{rows:?}");
            let error = record_initiating_rule_rows(
                &mut rows,
                12,
                34,
                56,
                |rule| {
                    calls.borrow_mut().push(("disposition", rule));
                    Some(InitiatingRuleDisposition::GroupFirst)
                },
                |rule| {
                    calls.borrow_mut().push(("members", rule));
                    members
                },
                "unused",
            );
            assert_eq!(*calls.borrow(), vec![("disposition", 34), ("members", 34)]);
            assert_eq!(
                error,
                members
                    .is_none()
                    .then_some(MissingInitiatingRuleMembers { category_src_idx: 12, rule_idx: 34 })
            );
            assert_eq!(format!("{rows:?}"), before);
        }
    }
}
