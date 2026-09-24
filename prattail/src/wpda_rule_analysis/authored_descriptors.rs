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
    try_build_collection_specs, CollectionAssemblyContext, CollectionAssemblyError,
    GeneratedCollectionSpecArm,
};
use super::collection::CollectionShape;
use super::factoring::emission::{
    try_build_factoring_emission_descriptors, FactoringEmissionDescriptors, FactoringEmissionError,
};
use super::factoring::{self, CategoryFactoring, PrefixAtomicObservation};
use super::mixfix::{self, MixfixFactoring};
use super::parikh::{try_build_parikh_descriptors, ParikhDescriptors};
use super::prefix_bucket::{PrefixBuckets, TryPrefixBucketContext};
use super::prefix_pattern::{NeutralPattern, NeutralPatternKey};
use crate::binding_power::{BindingPowerTable, InfixRuleInfo};
use mettail_ast::grammar_shapes::classify_unary_prefix_shape_in;
use mettail_ast::types::CollectionType;
use mettail_grammar_core::GrammarCoreV1;
use std::collections::HashMap;
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
    pub prefixes: Vec<PrefixBuckets<NeutralPattern, NeutralPatternKey>>,
    pub grouping_sources: Vec<Vec<u16>>,
    pub traversal_markers: TraversalMarkerTable,
    pub collections: Vec<GeneratedCollectionSpecArm>,
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
            prefixes,
            grouping_sources,
            traversal_markers,
            collections,
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
        prefixes,
        grouping_sources,
        traversal_markers,
        collections,
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
        prefixes,
        grouping_sources,
        traversal_markers,
        collections,
        prefix_partition,
        mixfix_partition,
        factoring_emission,
        parikh,
    })
}
