//! Owned assembly of the original WPDA derivation outputs.
//!
//! Source occurrences and synthesized local coordinates retain separate roles.
//! Every field comes from an existing shared macro-era worker. This artifact is
//! not a recognizer, transition image, or source reconstruction. The transition
//! emitter supplies its actual fork schedule later; descriptor indices are not
//! substitutes for emitted branch ordinals.
//!
//! Admission covers the whole finite helper domain before validation, derivation
//! and allocation. Cast participation is an explicit checked source observation,
//! never inferred from reduction code or defaulted when metadata is missing.

use super::atomic::AtomicDescriptor;
use super::authored::{AuthoredNameRef, AuthoredRuleReader};
use super::authored_collection::derive_authored_collection;
use super::authored_prefix::reader::OccurrenceReader;
use super::authored_prefix::{
    derive_category_prefix, with_authored_context, AuthoredPrefixError, Context,
};
use super::authored_synthesis::{AuthoredRulePayload, AuthoredSynthesisOutput};
use super::binder::optional::{BinderSyntaxObservation, BinderSyntaxReader};
use super::binder::rule::BinderRuleReader;
use super::binder::traversal::{TraversalBuildError, TraversalMarkerTable};
use super::binder::{try_build_prefix_bp_map_with, BinderShape};
use super::collection::assembly::{
    try_build_collection_specs, try_collect_structural_delimiters, CollectionAssemblyContext,
    CollectionAssemblyError, GeneratedCollectionSpecArm,
};
use super::collection::CollectionShape;
use super::factoring::emission::{
    try_build_factoring_emission_descriptors, FactoringEmissionDescriptors, FactoringEmissionError,
};
use super::factoring::{self, CategoryFactoring, PrefixAtomicObservation};
use super::mixfix::{self, MixfixFactoring};
use super::parikh::{try_build_parikh_descriptors, ParikhDescriptors};
use super::prefix::{try_first_set_of_category, try_source_ident_first_is_var_only, FirstToken};
use super::prefix_bucket::{PrefixBuckets, TryPrefixBucketContext};
use super::prefix_pattern::{NeutralPattern, NeutralPatternKey, PrefixPatternObservation};
use crate::binding_power::{BindingPowerTable, InfixRuleInfo};
use mettail_ast::grammar_shapes::classify_unary_prefix_shape_in;
use mettail_ast::types::CollectionType;
use mettail_grammar_core::GrammarCoreV1;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::convert::Infallible;

/// The original emitter's explicit switches and encoded constant domain.
/// Callers use the same configuration as the consuming transition emitter.
#[derive(Clone, Copy, Debug)]
pub struct DescriptorOptions {
    pub crosscat_lex_compat_gate: bool,
    pub prefix_factoring: bool,
    pub mixfix_factoring: bool,
    pub accept_continue: bool,
    pub recovery_base: u16,
    pub max_mixfix_slice: usize,
}

pub struct OwnedWpdaDescriptors<P> {
    pub synthesis: AuthoredSynthesisOutput<P>,
    pub original_occurrences: Vec<usize>,
    pub options: DescriptorOptions,
    pub binding_powers: BindingPowerTable,
    pub label_index: HashMap<(String, String), (u16, u16)>,
    pub prefix_binding_powers: HashMap<(u16, u16), u8>,
    pub leading_binding_powers: HashMap<(u16, u16), crate::binding_power::OperandBindingPowers>,
    pub prefixes: Vec<PrefixBuckets<NeutralPattern, NeutralPatternKey>>,
    pub grouping_sources: Vec<Vec<u16>>,
    pub traversal_markers: TraversalMarkerTable,
    pub collections: Vec<GeneratedCollectionSpecArm>,
    pub first_sets: Vec<Vec<FirstToken<NeutralPattern>>>,
    pub structural_delimiters: (BTreeSet<String>, BTreeSet<String>),
    pub transparent_projections: Vec<(u16, u16, u16)>,
    pub category_reachability: Vec<(u16, u16)>,
    pub projection_ident_var_only_sources: Vec<u16>,
    pub single_hop_coercions: BTreeMap<(u16, u16), Vec<(u16, u16)>>,
    pub prefix_partition: Vec<CategoryFactoring>,
    pub mixfix_partition: Vec<MixfixFactoring>,
    pub factoring_emission: FactoringEmissionDescriptors,
    pub parikh: ParikhDescriptors,
}

#[derive(Debug)]
pub enum AuthoredDescriptorsError<E> {
    Admission(E),
    Prefix(AuthoredPrefixError<E>),
    Traversal(TraversalBuildError<AuthoredPrefixError<E>>),
    Collection(CollectionAssemblyError<AuthoredPrefixError<E>>),
    Cast(E),
    Factoring(FactoringEmissionError),
    EmissionRefusals(Vec<String>),
    UnresolvedCoercions(Vec<(String, String)>),
    PositionIndexOverflow {
        category: usize,
        rule: usize,
        positions: usize,
    },
}

impl<E> From<AuthoredPrefixError<E>> for AuthoredDescriptorsError<E> {
    fn from(error: AuthoredPrefixError<E>) -> Self {
        Self::Prefix(error)
    }
}

impl<'reader, 'store, E> CollectionAssemblyContext<'store, AuthoredRulePayload>
    for Context<'reader, 'store, E>
{
    type Error = AuthoredPrefixError<E>;
    type Label = AuthoredNameRef<'store>;
    fn try_infix(
        &mut self,
        rule: &'store AuthoredRulePayload,
    ) -> Result<Option<InfixRuleInfo>, Self::Error> {
        self.infix_normalized(*rule)
    }
    fn try_collection(
        &mut self,
        rule: &'store AuthoredRulePayload,
    ) -> Result<Option<CollectionShape<CollectionType>>, Self::Error> {
        derive_authored_collection(self.rules, rule.rule, |_, _, _| Ok::<_, Infallible>(()))
            .map_err(AuthoredPrefixError::Collection)
    }
    fn try_binder(
        &mut self,
        rule: &'store AuthoredRulePayload,
    ) -> Result<Option<BinderShape>, Self::Error> {
        self.binder_shape(*rule)
    }
    fn try_label(&mut self, rule: &'store AuthoredRulePayload) -> Result<Self::Label, Self::Error> {
        Ok(self.rules.label(rule.rule))
    }
}

/// Assemble only complete successful results. The synthesis input must be the
/// existing worker's output for this Core and this exact source roster.
/// The cast callback observes indexed normalized/synthetic occurrences and must
/// report unavailable source evidence as an error, not `false`.
pub fn derive_authored_descriptors<P, E>(
    core: &GrammarCoreV1,
    original_occurrences: &[usize],
    synthesis: AuthoredSynthesisOutput<P>,
    options: DescriptorOptions,
    admit: impl FnOnce(
        &GrammarCoreV1,
        &[usize],
        &AuthoredSynthesisOutput<P>,
        DescriptorOptions,
    ) -> Result<(), E>,
    mut cast_participates: impl FnMut(&AuthoredRuleReader<'_>, AuthoredRulePayload) -> Result<bool, E>,
) -> Result<OwnedWpdaDescriptors<P>, AuthoredDescriptorsError<E>> {
    use AuthoredDescriptorsError as Error;
    admit(core, original_occurrences, &synthesis, options).map_err(Error::Admission)?;
    let parts = with_authored_context(core, original_occurrences, &synthesis, |reader, context| {
        // Check the actual Parikh positional encoding; do not wrap source positions.
        for (category, rules) in synthesis.per_category.iter().enumerate() {
            for (rule_index, rule) in rules.iter().enumerate() {
                if let Some(syntax) = reader.syntax_pattern(*rule) {
                    let positions = reader.sequence_len(syntax);
                    if positions > usize::from(u8::MAX) + 1 {
                        return Err(Error::PositionIndexOverflow {
                            category,
                            rule: rule_index,
                            positions,
                        });
                    }
                }
            }
        }
        // Include declaration-only/empty categories in the original census check.
        let categories = context.try_category_names()?;
        let binding_powers = context.try_binding_power_table()?;
        let label_index =
            super::census::build_label_index_with(&categories, &synthesis.per_category, |rule| {
                reader.label(*rule).to_string()
            });
        let prefix_binding_powers = try_build_prefix_bp_map_with(
            &synthesis.per_category,
            &binding_powers,
            |rule| {
                Ok::<_, AuthoredPrefixError<E>>(
                    classify_unary_prefix_shape_in(context.rules, rule.rule).is_some(),
                )
            },
            |rule| Ok((reader.category(*rule).to_string(), context.explicit_prefix_bp(*rule)?)),
        )?;
        let mut leading_binding_powers = HashMap::new();
        for (category, rows) in synthesis.per_category.iter().enumerate() {
            for (rule, payload) in rows.iter().enumerate() {
                let Some(powers) = context.explicit_operands(*payload)? else { continue; };
                if context.infix_normalized(*payload)?.is_some() { continue; }
                let Some(shape) = context.binder_shape(*payload)? else { continue; };
                if shape.leading_category.is_none() { continue; }
                let super::authored_synthesis::AuthoredRuleOrigin::User { production_index, .. } = payload.origin else {
                    return Err(Error::Prefix(AuthoredPrefixError::UnsupportedExplicitBinding("synthetic category-leading rule")));
                };
                let name = &categories[category];
                let exact_rhs = matches!(shape.positions.as_slice(),
                    [super::binder::BinderPosition::ParamParse { cat, collection: None }] if cat == name);
                if !core.productions[production_index].is_binary_juxtaposition()
                    || shape.leading_category.as_ref() != Some(name) || !exact_rhs {
                    return Err(Error::Prefix(AuthoredPrefixError::UnsupportedExplicitBinding("category-leading shape is not homogeneous binary juxtaposition")));
                }
                leading_binding_powers.insert((category as u16, rule as u16), powers);
            }
        }
        let mut prefixes = Vec::with_capacity(categories.len());
        let mut grouping_sources = Vec::with_capacity(categories.len());
        for (category, _) in categories.iter().enumerate() {
            let category_index = u16::try_from(category).expect("validated category width");
            prefixes.push(derive_category_prefix(
                reader,
                context,
                &synthesis,
                category_index,
                options.crosscat_lex_compat_gate,
            )?);
            grouping_sources.push(super::grouping::try_grouping_source_categories_for_result(
                &categories,
                context.originals,
                &synthesis.per_category,
                category,
                |rule| Ok::<_, AuthoredPrefixError<E>>(reader.category(*rule).to_string()),
                |rule| context.infix_original(*rule),
                |rule| {
                    Ok(match context.atomic(*rule)? {
                        AtomicDescriptor::CrossCatProjection { source_cat_name, .. } => {
                            Some(source_cat_name)
                        },
                        _ => None,
                    })
                },
            )?);
        }
        let traversal_markers =
            TraversalMarkerTable::try_build_with(&synthesis.per_category, |rule| {
                context.binder_shape(*rule)
            })
            .map_err(Error::Traversal)?;
        let collections = try_build_collection_specs(&categories, &synthesis.per_category, context)
            .map_err(Error::Collection)?;
        // These are the original collection-prefix predicate and delimiter
        // collector workers, not approximations from dispatch buckets.
        let mut first_sets = Vec::with_capacity(categories.len());
        for category in &categories {
            first_sets.push(try_first_set_of_category(category, reader, context)?);
        }
        let structural_delimiters =
            try_collect_structural_delimiters(&synthesis.per_category, context)
                .map_err(Error::Collection)?;
        let transparent_projections = super::rule_observation::transparent_projection_rules(
            reader,
            &synthesis.per_category,
            &categories,
        );
        let indexed: Vec<Vec<_>> = synthesis
            .per_category
            .iter()
            .map(|rules| {
                rules
                    .iter()
                    .enumerate()
                    .map(|(index, rule)| (index as u16, *rule))
                    .collect()
            })
            .collect();
        let (coercions, refusals) =
            super::rule_observation::single_hop_coercions(reader, &indexed, |source, rule| {
                categories
                    .iter()
                    .position(|category| category == source)
                    .map(|index| index as u16)
                    .ok_or_else(|| (source.to_owned(), reader.label(rule).to_string()))
            });
        if !refusals.is_empty() {
            return Err(Error::UnresolvedCoercions(refusals));
        }
        let single_hop_coercions = coercions
            .into_iter()
            .map(|((from, to), rules)| {
                ((from, to), rules.into_iter().map(|rule| (to, rule)).collect())
            })
            .collect();
        let idx_of = |name: &str| {
            categories
                .iter()
                .position(|category| category == name)
                .map(|i| i as u16)
        };
        let mut direct = BTreeSet::new();
        for rule in context.originals {
            if let Some(info) = context.infix_original(*rule)? {
                if info.is_cross_category && info.category != info.result_category {
                    if let (Some(from), Some(to)) =
                        (idx_of(&info.category), idx_of(&info.result_category))
                    {
                        if from != to {
                            direct.insert((from, to));
                        }
                    }
                }
            }
        }
        for &(from_cat, to_cat, _) in &transparent_projections {
            if from_cat != to_cat {
                direct.insert((from_cat, to_cat));
            }
        }
        let category_reachability =
            super::rule_observation::non_reflexive_category_reachability(direct);
        let mut projection_ident_var_only_sources = Vec::new();
        for (idx, cat) in categories.iter().enumerate() {
            let fs = try_first_set_of_category(cat, reader, context)?;
            let has_ident = fs
                .iter()
                .any(|ft| ft.pattern.mentions_ident() && ft.extra_guard.is_none());
            if has_ident && try_source_ident_first_is_var_only(cat, reader, context)? {
                projection_ident_var_only_sources.push(idx as u16);
            }
        }
        let discover = |category, rules: &[_]| {
            factoring::try_discover_prefix_members_with(
                &categories,
                category,
                rules,
                &prefix_binding_powers,
                |rule| {
                    Ok::<_, Error<E>>(match context.atomic(*rule)? {
                        AtomicDescriptor::CrossCatPrefixUnary { .. } => {
                            PrefixAtomicObservation::CrossCatPrefixUnary
                        },
                        AtomicDescriptor::CrossCatProjection { .. } => {
                            PrefixAtomicObservation::CrossCatProjection
                        },
                        AtomicDescriptor::NullaryLiteralRun {
                            trigger, trailing_literals, ..
                        } => PrefixAtomicObservation::NullaryLiteralRun {
                            trigger,
                            trailing_literals,
                        },
                        _ => PrefixAtomicObservation::Other,
                    })
                },
                |rule| context.binder_shape(*rule).map_err(Error::Prefix),
                |rule| {
                    Ok(reader
                        .syntax_pattern(*rule)
                        .and_then(|syntax| match reader.at(syntax, 0) {
                            Some(BinderSyntaxObservation::Literal(text)) => Some(text),
                            _ => None,
                        }))
                },
            )
        };
        let prefix_partition = if options.prefix_factoring {
            factoring::try_build_prefix_factoring_with(
                &synthesis.per_category,
                options.accept_continue,
                options.recovery_base,
                discover,
                |rule| cast_participates(context.rules, *rule).map_err(Error::Cast),
            )?
        } else {
            factoring::try_prefix_identity_partition(&synthesis.per_category, discover)?
        };
        let grouped = mixfix::group_ops_by_cat_terminal(&binding_powers, &categories, &label_index);
        let mixfix_partition = if options.prefix_factoring && options.mixfix_factoring {
            mixfix::try_build_mixfix_factoring_with(
                &categories,
                &synthesis.per_category,
                &prefix_partition,
                &grouped,
                options.max_mixfix_slice,
                options.recovery_base,
                |name, categories, _, _| {
                    categories
                        .iter()
                        .position(|value| value == name)
                        .map(|index| u16::try_from(index).expect("validated category width"))
                        .ok_or(())
                },
                |rule| cast_participates(context.rules, *rule).map_err(Error::Cast),
            )?
        } else {
            mixfix::mixfix_identity_partition(&grouped, options.max_mixfix_slice)
        };
        let refusals: Vec<_> = prefix_partition
            .iter()
            .flat_map(|value| &value.refusals)
            .chain(mixfix_partition.iter().flat_map(|value| &value.refusals))
            .cloned()
            .collect();
        if !refusals.is_empty() {
            return Err(Error::EmissionRefusals(refusals));
        }
        let factoring_emission = try_build_factoring_emission_descriptors(
            categories.len(),
            &prefix_partition,
            &mixfix_partition,
        )
        .map_err(Error::Factoring)?;
        let reference_reader = OccurrenceReader::new(context.rules);
        let parikh = try_build_parikh_descriptors(
            &reference_reader,
            context.originals,
            &categories,
            &synthesis.per_category,
            |rule| context.infix_original(*rule),
        )?;
        Ok((
            binding_powers,
            label_index,
            prefix_binding_powers,
            leading_binding_powers,
            prefixes,
            grouping_sources,
            traversal_markers,
            collections,
            first_sets,
            structural_delimiters,
            transparent_projections,
            category_reachability,
            projection_ident_var_only_sources,
            single_hop_coercions,
            prefix_partition,
            mixfix_partition,
            factoring_emission,
            parikh,
        ))
    })
    .map_err(Error::Prefix)??;
    let (
        binding_powers,
        label_index,
        prefix_binding_powers,
        leading_binding_powers,
        prefixes,
        grouping_sources,
        traversal_markers,
        collections,
        first_sets,
        structural_delimiters,
        transparent_projections,
        category_reachability,
        projection_ident_var_only_sources,
        single_hop_coercions,
        prefix_partition,
        mixfix_partition,
        factoring_emission,
        parikh,
    ) = parts;
    Ok(OwnedWpdaDescriptors {
        synthesis,
        original_occurrences: original_occurrences.to_vec(),
        options,
        binding_powers,
        label_index,
        prefix_binding_powers,
        leading_binding_powers,
        prefixes,
        grouping_sources,
        traversal_markers,
        collections,
        first_sets,
        structural_delimiters,
        transparent_projections,
        category_reachability,
        projection_ident_var_only_sources,
        single_hop_coercions,
        prefix_partition,
        mixfix_partition,
        factoring_emission,
        parikh,
    })
}
