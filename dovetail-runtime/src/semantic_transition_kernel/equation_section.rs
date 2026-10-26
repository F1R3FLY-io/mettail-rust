//! Execute a source-certified equation section using Dovetail's existing engines.
//!
//! Only the certificate's reducing equation orientations enter this private
//! graph. Guest operational rewrites and native callbacks never enter it. A
//! selected representative is accepted only after the same compiled matcher
//! establishes irreducibility in a fresh, unmerged graph. Selection therefore
//! chooses a representative of a proved equation quotient, not a guest
//! transition or a parser alternative.

use super::*;
use crate::theory_image_compiler::flat_pattern_from_roots;
use dovetail::extract::{Derivation, ExtractionCompleteness, Extractor};
use dovetail::rules::{CompiledRuleSet, Pattern, RewriteRule, SatReport, SaturationOutcome};
use dovetail::set_automaton::FlatPatternNode;
use mettail_grammar_core::VerifiedSourceEquationSectionV1;
use rigail::TropicalWeight;
use std::rc::Rc;

mod carrier;
pub use carrier::{EquationSectionCarrierAdmission, VerifiedEquationSectionCarrier};

/// Existing engine limits and the separately accounted representation boundary.
/// `term.work` counts validation, traversal and publication work; it is NOT an
/// instruction budget for saturation/extraction, whose existing APIs expose
/// node/iteration limits rather than per-operation cancellation or metering.
#[derive(Clone, Copy, Debug)]
pub struct EquationSectionLimits {
    pub term: SemanticInputLimits,
    pub egraph_nodes: usize,
    /// Shared across saturation and all raw/collection probes in every round.
    pub saturation_iterations: usize,
    /// Counts unfolded tree occurrences, including repeated edges in a DAG.
    /// The adapter also requires fewer than 2^53 occurrences so unit-weight
    /// comparisons stay exact. This is a completeness bound, not a proof of
    /// irreducibility: the latter is checked independently after extraction.
    pub unfolded_occurrences: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EquationSectionFailureKind {
    Boundary(SemanticMatchUndetermined),
    Saturation(SaturationOutcome),
    IncompleteExtraction,
    NotIrreducible,
    OccurrenceLimitExceeded,
    NonDecreasingCoordination,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EquationSectionFailure {
    pub reason: EquationSectionFailureKind,
    pub boundary_work: u64,
}

/// Actual engine calls in one equation/collection round. Class identifiers are
/// local to each call's graph, not standalone replay or native funding evidence.
#[derive(Debug)]
pub struct EquationSectionPhaseReport {
    pub saturation: SatReport,
    pub raw_irreducibility: SatReport,
    /// Absent only when the selected raw representative has no collections.
    /// A positive probe stays here even when its private graph feeds the next
    /// round. Only a converged zero-merge probe permits publication.
    pub collection_irreducibility: Option<SatReport>,
}

/// The equation/collection model proves successful combined normal forms are
/// unique under its exact-key and authenticated-profile premises. This report
/// does not claim totality for inputs whose normalized Map keys collide.
pub struct EquationSectionReport {
    pub normal_form: SemanticTransitionInput,
    pub boundary_work: u64,
    pub phases: Vec<EquationSectionPhaseReport>,
}

impl std::fmt::Debug for EquationSectionReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EquationSectionReport")
            .field("root", &self.normal_form.root)
            .field("boundary_work", &self.boundary_work)
            .field("phases", &self.phases)
            .finish()
    }
}

/// Compile once from an immutable source/image certificate; reuse across terms.
pub struct SourceEquationSection<'a> {
    certificate: &'a VerifiedSourceEquationSectionV1<'a>,
    rules: CompiledRuleSet<FramedSemanticOperator>,
    collection_operators: HashMap<FramedSemanticOperator, TheoryImageOperatorV1>,
}

impl<'a> SourceEquationSection<'a> {
    pub fn restore(
        certificate: &'a VerifiedSourceEquationSectionV1<'a>,
    ) -> Result<Self, SemanticMatchUndetermined> {
        let mut rules = Vec::new();
        rules
            .try_reserve_exact(certificate.witnesses().len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        for witness in certificate.witnesses() {
            // Source origins, not an assumed program-index arithmetic layout,
            // bind each selected direction to its authenticated source row.
            let origin = TheoryRuleOriginV1::Equation {
                source: witness.equation,
                direction: witness.direction,
            };
            let mut programs = certificate
                .semantic_image()
                .rules
                .iter()
                .filter(|program| program.origin == origin);
            let program = programs
                .next()
                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
            if programs.next().is_some() {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            rules.push(RewriteRule {
                lhs: section_pattern(program, program.left)?,
                rhs: section_pattern(program, program.right)?,
                label: Some(format!(
                    "equation-section:{}:{:?}",
                    witness.equation, witness.direction
                )),
            });
        }
        // Resolve exact operators once from the authenticated image. No new
        // operator decoder or collection policy is needed at reconstruction.
        let mut collection_operators = HashMap::default();
        for sort in &certificate.semantic_image().sorts {
            if let TheorySortKindImageV1::Collection { kind, element, .. } = &sort.kind {
                let operator = TheoryImageOperatorV1::Collection {
                    sort: sort.id,
                    element: *element,
                    kind: *kind,
                };
                collection_operators
                    .try_reserve(1)
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                collection_operators.insert(theory_operator_to_machine(&operator), operator);
            }
        }
        Ok(Self {
            certificate,
            rules: CompiledRuleSet::from_rewrites(rules),
            collection_operators,
        })
    }

    pub fn normalize<C: FnMut() -> bool>(
        &self,
        input: SemanticTransitionInput,
        limits: EquationSectionLimits,
        is_cancelled: C,
    ) -> Result<EquationSectionReport, EquationSectionFailure> {
        self.normalize_in_sort(input, self.certificate.roles().sort, limits, is_cancelled)
    }

    /// Normalize a selected carrier of the same authenticated source image.
    /// The root sort may differ from the equation-role sort: equations apply
    /// within its typed children, while both boundaries retain the root sort.
    /// This bounded operation does not certify totality for that whole carrier.
    pub fn normalize_in_sort<C: FnMut() -> bool>(
        &self,
        input: SemanticTransitionInput,
        root_sort: TheorySortId,
        limits: EquationSectionLimits,
        mut is_cancelled: C,
    ) -> Result<EquationSectionReport, EquationSectionFailure> {
        let mut work = input.admission_work;
        let result = self.normalize_inner(input, root_sort, limits, &mut work, &mut is_cancelled);
        result.map_err(|reason| EquationSectionFailure { reason, boundary_work: work })
    }

    fn normalize_inner<C: FnMut() -> bool>(
        &self,
        input: SemanticTransitionInput,
        root_sort: TheorySortId,
        limits: EquationSectionLimits,
        work: &mut u64,
        cancelled: &mut C,
    ) -> Result<EquationSectionReport, EquationSectionFailureKind> {
        use EquationSectionFailureKind::{
            Boundary, IncompleteExtraction, NotIrreducible, Saturation,
        };
        if *work > limits.term.work {
            return Err(Boundary(SemanticMatchUndetermined::WorkBudgetExhausted));
        }
        if input.egraph.node_count() > limits.term.nodes
            || input.exact_key.len() > limits.term.bytes
        {
            return Err(Boundary(SemanticMatchUndetermined::InputLimitExceeded));
        }
        self.validate(&input, root_sort, limits.term, work, cancelled)
            .map_err(Boundary)?;
        let mut previous_count = unfolded_count(&input, limits, work, cancelled)?;
        let mut remaining_iterations = limits.saturation_iterations;
        let mut phases = Vec::new();
        let mut root = input.root;
        let mut graph = input.egraph;
        loop {
            seed_section_constants(&mut graph, self.certificate, limits.egraph_nodes)
                .map_err(Boundary)?;
            charge_work(work, limits.term.work, cancelled).map_err(Boundary)?;
            let saturation = self.saturate(&mut graph, &mut remaining_iterations, usize::MAX)?;
            if saturation.outcome != SaturationOutcome::Converged {
                return Err(Saturation(saturation.outcome));
            }
            charge_work(work, limits.term.work, cancelled).map_err(Boundary)?;
            let selected = Extractor::new(&graph, |_| TropicalWeight::new(1.0)).funded_best(root);
            if selected.completeness != ExtractionCompleteness::Complete {
                return Err(IncompleteExtraction);
            }
            let selected = selected.value.ok_or(IncompleteExtraction)?;
            drop(graph);
            let (mut fresh, raw_root, has_collections) =
                project_selected(&selected, self, false, limits.term, work, cancelled)
                    .map_err(Boundary)?;
            seed_section_constants(&mut fresh, self.certificate, limits.egraph_nodes)
                .map_err(Boundary)?;
            charge_work(work, limits.term.work, cancelled).map_err(Boundary)?;
            // The raw equation result is checked BEFORE collection changes.
            // In this fresh graph every redex would merge distinct classes.
            let raw_irreducibility = self.saturate(&mut fresh, &mut remaining_iterations, 1)?;
            if raw_irreducibility.stats.total_merges != 0 {
                return Err(NotIrreducible);
            }
            if raw_irreducibility.outcome != SaturationOutcome::Converged {
                return Err(Saturation(raw_irreducibility.outcome));
            }
            let (canonical_graph, canonical_root) = if has_collections {
                drop(fresh);
                let (canonical, root, _) =
                    project_selected(&selected, self, true, limits.term, work, cancelled)
                        .map_err(Boundary)?;
                (canonical, root)
            } else {
                (fresh, raw_root)
            };
            drop(selected);
            let mut canonical = self.admit_result(
                canonical_graph,
                canonical_root,
                root_sort,
                limits.term,
                work,
                cancelled,
            )?;
            let count = unfolded_count(&canonical, limits, work, cancelled)?;
            if count > previous_count || (!phases.is_empty() && count == previous_count) {
                return Err(EquationSectionFailureKind::NonDecreasingCoordination);
            }
            // Capture the logical source measure BEFORE a probe can merge its
            // graph. A positive probe is retained, never re-admitted as a fresh
            // exact input, and the next completed cycle must strictly decrease.
            previous_count = count;
            let collection_irreducibility = if has_collections {
                seed_section_constants(
                    &mut canonical.egraph,
                    self.certificate,
                    limits.egraph_nodes,
                )
                .map_err(Boundary)?;
                charge_work(work, limits.term.work, cancelled).map_err(Boundary)?;
                Some(self.saturate(&mut canonical.egraph, &mut remaining_iterations, 1)?)
            } else {
                None
            };
            let continue_round = if let Some(probe) = &collection_irreducibility {
                if probe.outcome == SaturationOutcome::NodeLimit
                    || (probe.stats.total_merges == 0
                        && probe.outcome != SaturationOutcome::Converged)
                {
                    return Err(Saturation(probe.outcome));
                }
                probe.stats.total_merges != 0
            } else {
                false
            };
            phases
                .try_reserve(1)
                .map_err(|_| Boundary(SemanticMatchUndetermined::AllocationFailed))?;
            phases.push(EquationSectionPhaseReport {
                saturation,
                raw_irreducibility,
                collection_irreducibility,
            });
            if continue_round {
                root = canonical.root;
                graph = canonical.egraph;
                continue;
            }
            if has_collections {
                // Drop probe-only unreachable seeds using existing admission;
                // a returned term must satisfy the same public input limits.
                canonical = self.admit_result(
                    canonical.egraph,
                    canonical.root,
                    root_sort,
                    limits.term,
                    work,
                    cancelled,
                )?;
            }
            canonical.admission_work = *work;
            return Ok(EquationSectionReport {
                normal_form: canonical,
                boundary_work: *work,
                phases,
            });
        }
    }

    fn saturate(
        &self,
        graph: &mut EGraph<FramedSemanticOperator>,
        remaining_iterations: &mut usize,
        requested: usize,
    ) -> Result<SatReport, EquationSectionFailureKind> {
        let report = graph.saturate_compiled(&self.rules, requested.min(*remaining_iterations));
        *remaining_iterations = remaining_iterations
            .checked_sub(report.stats.iterations)
            .ok_or(EquationSectionFailureKind::Boundary(
                SemanticMatchUndetermined::InvalidImageEvidence,
            ))?;
        Ok(report)
    }

    fn admit_result<C: FnMut() -> bool>(
        &self,
        graph: EGraph<FramedSemanticOperator>,
        root: EClassId,
        root_sort: TheorySortId,
        limits: SemanticInputLimits,
        work: &mut u64,
        cancelled: &mut C,
    ) -> Result<SemanticTransitionInput, EquationSectionFailureKind> {
        use EquationSectionFailureKind::Boundary;
        let remaining = limits
            .work
            .checked_sub(*work)
            .ok_or(Boundary(SemanticMatchUndetermined::WorkBudgetExhausted))?;
        let (decision, admission_work) = SemanticTransitionInput::admit_accounted(
            graph,
            root,
            SemanticInputLimits { work: remaining, ..limits },
            &mut *cancelled,
        );
        absorb_reported_work(work, limits.work, admission_work).map_err(Boundary)?;
        let mut normal_form = match decision {
            SemanticInputDecision::Proven(input) => input,
            SemanticInputDecision::Refuted(_) => {
                return Err(Boundary(SemanticMatchUndetermined::InvalidImageEvidence))
            },
            SemanticInputDecision::Undetermined { reason, .. } => return Err(Boundary(reason)),
        };
        self.validate(&normal_form, root_sort, limits, work, cancelled)
            .map_err(Boundary)?;
        normal_form.admission_work = *work;
        Ok(normal_form)
    }

    fn validate<C: FnMut() -> bool>(
        &self,
        input: &SemanticTransitionInput,
        root_sort: TheorySortId,
        limits: SemanticInputLimits,
        work: &mut u64,
        cancelled: &mut C,
    ) -> Result<(), SemanticMatchUndetermined> {
        let mut validator = HornEvaluator {
            image: self.certificate.semantic_image(),
            egraph: &input.egraph,
            work: *work,
            work_limit: limits.work,
            ground_key_nodes: limits.nodes,
            ground_key_bytes: limits.bytes,
            ground_key_limit_reason: SemanticMatchUndetermined::InputLimitExceeded,
            is_cancelled: cancelled,
            synthetic_terms: Vec::new(),
            lexical_scopes: Vec::new(),
            collection_states: Vec::new(),
            comprehension_states: Vec::new(),
            derived_collections: Vec::new(),
            next_activation: 0,
        };
        let result = validator.validate_ground_term(input.root, root_sort);
        *work = validator.work;
        result
    }
}

// A representation adapter only: source compilation and variable naming stay
// in flat_pattern_from_roots; matching stays in CompiledRuleSet. The certified
// schemas have fixed depth, independent of arbitrary guest input depth/arity.
fn section_pattern(
    program: &TheoryRuleProgramV1,
    root: mettail_grammar_core::TheoryTermId,
) -> Result<Pattern<FramedSemanticOperator>, SemanticMatchUndetermined> {
    let flat = flat_pattern_from_roots(&program.terms, &[root], None, program.id.0)
        .map_err(|_| SemanticMatchUndetermined::InvalidImageEvidence)?;
    let mut patterns: Vec<Pattern<FramedSemanticOperator>> = Vec::new();
    patterns
        .try_reserve_exact(flat.nodes.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    for node in flat.nodes {
        patterns.push(match node {
            FlatPatternNode::Var(name) => Pattern::Var(name),
            FlatPatternNode::App { op, args } => {
                let mut children = Vec::new();
                children
                    .try_reserve_exact(args.len())
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                for child in args {
                    children.push(
                        patterns
                            .get(child)
                            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?
                            .clone(),
                    );
                }
                Pattern::App {
                    op: theory_operator_to_machine(&op),
                    args: children,
                }
            },
            _ => return Err(SemanticMatchUndetermined::InvalidImageEvidence),
        });
    }
    patterns
        .get(flat.root)
        .cloned()
        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)
}

fn seed_section_constants(
    graph: &mut EGraph<FramedSemanticOperator>,
    certificate: &VerifiedSourceEquationSectionV1<'_>,
    node_limit: usize,
) -> Result<(), SemanticMatchUndetermined> {
    let remaining = node_limit
        .checked_sub(graph.node_count())
        .ok_or(SemanticMatchUndetermined::EGraphNodeBudgetExhausted)?;
    if !graph.set_additional_node_budget(remaining) {
        return Err(SemanticMatchUndetermined::EGraphNodeBudgetExhausted);
    }
    for constructor in [certificate.roles().zero, certificate.roles().unit] {
        graph
            .try_add_with_budget(ENode::new(
                theory_operator_to_machine(&TheoryImageOperatorV1::Constructor(constructor)),
                Vec::new(),
            ))
            .ok_or(SemanticMatchUndetermined::EGraphNodeBudgetExhausted)?;
    }
    Ok(())
}

fn checked_occurrences(
    total: u64,
    child: u64,
    limit: u64,
) -> Result<u64, EquationSectionFailureKind> {
    total
        .checked_add(child)
        .filter(|count| *count <= limit.min((1_u64 << 53) - 1))
        .ok_or(EquationSectionFailureKind::OccurrenceLimitExceeded)
}

fn unfolded_count<C: FnMut() -> bool>(
    input: &SemanticTransitionInput,
    limits: EquationSectionLimits,
    work: &mut u64,
    cancelled: &mut C,
) -> Result<u64, EquationSectionFailureKind> {
    use EquationSectionFailureKind::Boundary;
    let mut counts = HashMap::default();
    let mut pending = vec![(input.root, false)];
    while let Some((class, expanded)) = pending.pop() {
        charge_work(work, limits.term.work, cancelled).map_err(Boundary)?;
        if counts.contains_key(&class) {
            continue;
        }
        let [node] = input.egraph.nodes(class) else {
            return Err(Boundary(SemanticMatchUndetermined::InvalidImageEvidence));
        };
        if expanded {
            let mut count = checked_occurrences(0, 1, limits.unfolded_occurrences)?;
            for child in &node.children {
                charge_work(work, limits.term.work, cancelled).map_err(Boundary)?;
                count = checked_occurrences(
                    count,
                    *counts
                        .get(child)
                        .ok_or(Boundary(SemanticMatchUndetermined::InvalidImageEvidence))?,
                    limits.unfolded_occurrences,
                )?;
            }
            counts
                .try_reserve(1)
                .map_err(|_| Boundary(SemanticMatchUndetermined::AllocationFailed))?;
            counts.insert(class, count);
        } else {
            pending
                .try_reserve(
                    node.children
                        .len()
                        .checked_add(1)
                        .ok_or(Boundary(SemanticMatchUndetermined::InputLimitExceeded))?,
                )
                .map_err(|_| Boundary(SemanticMatchUndetermined::AllocationFailed))?;
            pending.push((class, true));
            pending.extend(node.children.iter().rev().map(|child| (*child, false)));
        }
    }
    counts
        .get(&input.root)
        .copied()
        .ok_or(Boundary(SemanticMatchUndetermined::InvalidImageEvidence))
}

// Reconstruct precisely one chosen derivation, preserving ordered and repeated
// child edges. Rc addresses are only traversal memoization, never term identity;
// the existing EGraph exact-key interner decides structural equality.
fn project_selected<C: FnMut() -> bool>(
    root: &Rc<Derivation<FramedSemanticOperator, TropicalWeight>>,
    section: &SourceEquationSection<'_>,
    canonicalize: bool,
    limits: SemanticInputLimits,
    work: &mut u64,
    cancelled: &mut C,
) -> Result<(EGraph<FramedSemanticOperator>, EClassId, bool), SemanticMatchUndetermined> {
    let mut graph = EGraph::with_config(EGraphConfig { max_nodes: limits.nodes });
    let mut mapped = HashMap::default();
    let mut pending = vec![(root, false)];
    let mut bytes = 0usize;
    let mut has_collections = false;
    while let Some((term, expanded)) = pending.pop() {
        charge_work(work, limits.work, cancelled)?;
        let address = Rc::as_ptr(term);
        if mapped.contains_key(&address) {
            continue;
        }
        if expanded {
            let mut children = Vec::new();
            children
                .try_reserve_exact(term.children.len())
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            for child in &term.children {
                charge_work(work, limits.work, cancelled)?;
                children.push(
                    *mapped
                        .get(&Rc::as_ptr(child))
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?,
                );
            }
            if let Some(operator) = section.collection_operators.get(&term.op) {
                has_collections = true;
                if canonicalize {
                    canonicalize_collection_children(
                        CollectionCanonicalization {
                            image: section.certificate.semantic_image(),
                            operator,
                            // Preserve the existing marker; never infer Set
                            // versus Map mode from the entry count.
                            pathmap_mode: None,
                            limits: TermConstructionLimits {
                                work: limits.work,
                                nodes: limits.nodes,
                                bytes: limits.bytes,
                            },
                        },
                        &mut graph,
                        &mut children,
                        work,
                        cancelled,
                    )?;
                }
            }
            let node = ENode::new(term.op.clone(), children);
            bytes = bytes
                .checked_add(
                    publication_node_bytes(&node)
                        .ok_or(SemanticMatchUndetermined::OutputLimitExceeded)?,
                )
                .filter(|total| *total <= limits.bytes)
                .ok_or(SemanticMatchUndetermined::OutputLimitExceeded)?;
            let class = graph
                .try_add_with_budget(node)
                .ok_or(SemanticMatchUndetermined::EGraphNodeBudgetExhausted)?;
            mapped
                .try_reserve(1)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            mapped.insert(address, class);
        } else {
            pending
                .try_reserve(
                    term.children
                        .len()
                        .checked_add(1)
                        .ok_or(SemanticMatchUndetermined::OutputLimitExceeded)?,
                )
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            pending.push((term, true));
            pending.extend(term.children.iter().rev().map(|child| (child, false)));
        }
    }
    let root = *mapped
        .get(&Rc::as_ptr(root))
        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
    Ok((graph, root, has_collections))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn occurrence_arithmetic_refuses_overflow_and_inexact_weights() {
        assert_eq!(
            checked_occurrences(u64::MAX, 1, u64::MAX),
            Err(EquationSectionFailureKind::OccurrenceLimitExceeded)
        );
        assert_eq!(
            checked_occurrences((1 << 53) - 1, 1, u64::MAX),
            Err(EquationSectionFailureKind::OccurrenceLimitExceeded)
        );
        assert_eq!(checked_occurrences((1 << 53) - 2, 1, u64::MAX), Ok((1 << 53) - 1));
        assert_eq!(
            checked_occurrences(1, 2, 2),
            Err(EquationSectionFailureKind::OccurrenceLimitExceeded)
        );
    }
}
