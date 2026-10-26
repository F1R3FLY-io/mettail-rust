//! The finite, source-exact part of a Cost(G) funding interpretation.
//!
//! The checked roster establishes the induction domain for a structural
//! grade fold: every
//! consumed rewrite grade is a closed generator (or unit), every grade-sort
//! constructor is unit/product/a closed generator, and exactly one selected
//! compiled projection rule covers each non-unit generator.  The runtime must
//! still apply those rules to the retained roots, check their complete output
//! rosters and receipts, fold product with the host signature monoid, and
//! verify the resulting demand against live host resource logic. The finite
//! verifier below certifies the selected generator programs' fixed template;
//! it does not perform that runtime fold or authorize any supply.

use std::collections::BTreeMap;

use crate::{
    CostImageV1, FundingProjectionSelectorV2, FundingProjectionVerifierV2, LanguageCoreV1,
    ProjectedLanguageCoreV1, ProjectedTheorySemanticImageV1, ProjectionDirectionV1,
    ProjectionHostCompoundProfileRecordV2, ProjectionRelationBodyImageV1, TheoryConstructorId,
    TheoryImageAdmissionLimits, TheoryImageOperatorV1, TheoryImageTermFormV1,
    TheoryRuleDispositionV1, TheoryRuleOriginV1, TheoryRuleProgramId, TheorySemanticImageV1,
    TheorySortId, TheorySortKindImageV1, TheoryTermId,
};

/// This ABI denotes the host `DefaultResourceLogic`/`delta_sigma` judgment
/// tested against the MeTTaIL adapter, not a guest-supplied numeric gas rule.
pub const FINITE_COST_RESOURCE_LOGIC_ABI_V2: &str = "rho-delta-sigma/finite-grade-v2";
pub const FINITE_COST_BOUND_VERIFIER_ABI_V2: &str = "rho-demand-bound/finite-grade-v2";
pub const FINITE_COST_PROJECTION_PROOF_ABI_V2: &str = "cost-g/nullary-fixed-template-v2";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckedGradeGeneratorV2 {
    constructor: TheoryConstructorId,
    projection_program: TheoryRuleProgramId,
    source_occurrence: u32,
}

/// A checked induction roster, not a proof that host demand is funded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedFiniteGradeRosterV2 {
    grade_sort: TheorySortId,
    unit: TheoryConstructorId,
    product: TheoryConstructorId,
    generators: Vec<CheckedGradeGeneratorV2>,
}

impl CheckedGradeGeneratorV2 {
    pub fn constructor(&self) -> TheoryConstructorId {
        self.constructor
    }

    pub fn projection_program(&self) -> TheoryRuleProgramId {
        self.projection_program
    }

    pub fn source_occurrence(&self) -> u32 {
        self.source_occurrence
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FiniteGradeRosterErrorV2 {
    InvalidSource,
    InvalidSelector,
    ImageMismatch,
    OpenGradeSort,
    InvalidUnit,
    InvalidProduct,
    OpenGenerator,
    GradeRewrite,
    DynamicRuleGrade,
    MissingGenerator,
    DuplicateGenerator,
    UnexpectedProjectionRule,
    OpenProjectionRule,
    LimitExceeded,
}

fn nullary_constructor(
    terms: &[crate::TheoryImageTermNodeV1],
    root: TheoryTermId,
) -> Option<TheoryConstructorId> {
    let node = terms.get(root.0 as usize)?;
    match &node.form {
        TheoryImageTermFormV1::Apply {
            operator: TheoryImageOperatorV1::Constructor(constructor),
            arguments,
            slots,
            remainder,
            pathmap_mode,
        } if arguments.is_empty()
            && slots.is_empty()
            && remainder.is_none()
            && pathmap_mode.is_none() =>
        {
            Some(*constructor)
        },
        _ => None,
    }
}

fn closed_constructor_template(terms: &[crate::TheoryImageTermNodeV1], root: TheoryTermId) -> bool {
    // A closed-looking cycle is not a finite template. Track the active path
    // separately from completed DAG nodes so sharing is accepted, but a back
    // edge is refused without recursive Rust calls.
    let mut state = Vec::new();
    if state.try_reserve_exact(terms.len()).is_err() {
        return false;
    }
    state.resize(terms.len(), 0_u8);
    let mut work = vec![(root, false)];
    while let Some((next, expanded)) = work.pop() {
        let index = next.0 as usize;
        let Some(node) = terms.get(index) else {
            return false;
        };
        if expanded {
            state[index] = 2;
            continue;
        }
        if state[index] == 2 {
            continue;
        }
        if state[index] == 1 {
            return false;
        }
        let TheoryImageTermFormV1::Apply {
            operator: TheoryImageOperatorV1::Constructor(_),
            arguments,
            slots,
            remainder: None,
            pathmap_mode: None,
        } = &node.form
        else {
            return false;
        };
        if !slots.is_empty() || work.try_reserve(arguments.len().saturating_add(1)).is_err() {
            return false;
        }
        state[index] = 1;
        work.push((next, true));
        work.extend(arguments.iter().rev().copied().map(|child| (child, false)));
    }
    true
}

fn constructor_children(
    terms: &[crate::TheoryImageTermNodeV1],
    root: TheoryTermId,
    sort: TheorySortId,
    constructor: TheoryConstructorId,
) -> Option<&[TheoryTermId]> {
    let node = terms.get(root.0 as usize)?;
    if node.sort != sort {
        return None;
    }
    match &node.form {
        TheoryImageTermFormV1::Apply {
            operator: TheoryImageOperatorV1::Constructor(actual),
            arguments,
            slots,
            remainder: None,
            pathmap_mode: None,
        } if *actual == constructor && slots.is_empty() => Some(arguments),
        _ => None,
    }
}

/// For this versioned fragment each generator denotes exactly one unit of
/// demand on the host's closed `#Nil` signature lane. The body is `Nil`, so a
/// guest projection cannot smuggle a send, receive, or supply-bearing process
/// into the demand. Runtime product folding must use canonical CostSig
/// composition; this checker never treats Par concatenation as grade product.
fn fixed_signed_nil_template(
    terms: &[crate::TheoryImageTermNodeV1],
    root: TheoryTermId,
    proc_sort: TheorySortId,
    sig_sort: TheorySortId,
    signed: TheoryConstructorId,
    nil: TheoryConstructorId,
    hash: TheoryConstructorId,
) -> bool {
    let Some([body, signature]) = constructor_children(terms, root, proc_sort, signed) else {
        return false;
    };
    if !matches!(constructor_children(terms, *body, proc_sort, nil), Some([])) {
        return false;
    }
    let Some([hash_body]) = constructor_children(terms, *signature, sig_sort, hash) else {
        return false;
    };
    matches!(constructor_children(terms, *hash_body, proc_sort, nil), Some([]))
}

fn selected_host_sort(
    base: &TheorySemanticImageV1,
    image: &ProjectedTheorySemanticImageV1,
    host: &ProjectionHostCompoundProfileRecordV2,
    name: &str,
) -> Option<TheorySortId> {
    let index = host
        .payload
        .sorts
        .iter()
        .position(|sort| sort.name == name)?;
    let absolute = base.sorts.len().checked_add(index)?;
    let id = TheorySortId(u32::try_from(absolute).ok()?);
    (image.execution.sorts.get(absolute)?.id == id).then_some(id)
}

fn selected_host_constructor(
    base: &TheorySemanticImageV1,
    image: &ProjectedTheorySemanticImageV1,
    host: &ProjectionHostCompoundProfileRecordV2,
    category: &str,
    name: &str,
) -> Option<TheoryConstructorId> {
    let label = format!("{}::{category}::{name}", host.payload.language_name);
    if !host
        .payload
        .codec
        .descriptor
        .operators
        .iter()
        .any(|route| route.label == label)
    {
        return None;
    }
    let index = host
        .payload
        .constructors
        .iter()
        .position(|constructor| constructor.name == label)?;
    let absolute = base.constructors.len().checked_add(index)?;
    let id = TheoryConstructorId(u32::try_from(absolute).ok()?);
    (image.execution.constructors.get(absolute)?.id == id).then_some(id)
}

/// A trusted, executable proof checker for the explicitly finite/nullary
/// Cost(G) fragment. The digest commits the checked law and this checker, but
/// the digest alone grants no authority: `verify_selected_projection` checks
/// the exact source roster and every selected compiled host program.
pub struct FiniteNullaryCostFundingVerifierV2;

impl FiniteNullaryCostFundingVerifierV2 {
    pub fn proof_commitment() -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"cost-g/nullary-fixed-template-v2/checker-and-rocq\0");
        hasher.update(include_bytes!("finite_grade_projection.rs"));
        hasher
            .update(include_bytes!("../../formal/rocq/rho_bridge/theories/FiniteCostGradeFold.v"));
        *hasher.finalize().as_bytes()
    }
}

impl FundingProjectionVerifierV2 for FiniteNullaryCostFundingVerifierV2 {
    fn resource_logic_abi(&self) -> &str {
        FINITE_COST_RESOURCE_LOGIC_ABI_V2
    }

    fn bound_verifier_abi(&self) -> &str {
        FINITE_COST_BOUND_VERIFIER_ABI_V2
    }

    fn projection_proof_abi(&self) -> &str {
        FINITE_COST_PROJECTION_PROOF_ABI_V2
    }

    fn projection_proof_commitment(&self) -> [u8; 32] {
        Self::proof_commitment()
    }

    fn verify_selected_projection(
        &self,
        selector: &FundingProjectionSelectorV2,
        projected: &ProjectedLanguageCoreV1,
        base: &TheorySemanticImageV1,
        cost: &CostImageV1,
        image: &ProjectedTheorySemanticImageV1,
        host: &ProjectionHostCompoundProfileRecordV2,
    ) -> bool {
        if selector.resource_logic_abi != self.resource_logic_abi()
            || selector.bound_verifier_abi != self.bound_verifier_abi()
            || selector.projection_proof_abi != self.projection_proof_abi()
            || selector.projection_proof_commitment != self.projection_proof_commitment()
            || host.validate().is_err()
            || image.host_signature_fingerprint != host.claimed_digests.signature_fingerprint
            || image.host_codec_profile_fingerprint
                != host.claimed_digests.codec_profile_fingerprint
        {
            return false;
        }
        let Ok(roster) = CheckedFiniteGradeRosterV2::check(
            selector,
            projected,
            base,
            cost,
            image,
            TheoryImageAdmissionLimits::default(),
        ) else {
            return false;
        };
        let Some(proc_sort) = selected_host_sort(base, image, host, "Proc") else {
            return false;
        };
        let Some(sig_sort) = selected_host_sort(base, image, host, "CostSig") else {
            return false;
        };
        let Some(signed) = selected_host_constructor(base, image, host, "Proc", "PCostSignedTerm")
        else {
            return false;
        };
        let Some(nil) = selected_host_constructor(base, image, host, "Proc", "PZero") else {
            return false;
        };
        let Some(hash) = selected_host_constructor(base, image, host, "CostSig", "CostSigHash")
        else {
            return false;
        };
        if image
            .execution
            .constructors
            .get(signed.0 as usize)
            .map(|item| (item.domain.as_slice(), item.codomain))
            != Some(([proc_sort, sig_sort].as_slice(), proc_sort))
            || image
                .execution
                .constructors
                .get(nil.0 as usize)
                .map(|item| (item.domain.as_slice(), item.codomain))
                != Some(([].as_slice(), proc_sort))
            || image
                .execution
                .constructors
                .get(hash.0 as usize)
                .map(|item| (item.domain.as_slice(), item.codomain))
                != Some(([proc_sort].as_slice(), sig_sort))
        {
            return false;
        }
        roster.generators.iter().all(|generator| {
            image
                .execution
                .rules
                .get(generator.projection_program.0 as usize)
                .is_some_and(|program| {
                    fixed_signed_nil_template(
                        &program.terms,
                        program.right,
                        proc_sort,
                        sig_sort,
                        signed,
                        nil,
                        hash,
                    )
                })
        })
    }
}

impl CheckedFiniteGradeRosterV2 {
    pub fn grade_sort(&self) -> TheorySortId {
        self.grade_sort
    }

    pub fn unit(&self) -> TheoryConstructorId {
        self.unit
    }

    pub fn product(&self) -> TheoryConstructorId {
        self.product
    }

    pub fn generators(&self) -> &[CheckedGradeGeneratorV2] {
        &self.generators
    }

    pub fn generator(&self, constructor: TheoryConstructorId) -> Option<&CheckedGradeGeneratorV2> {
        self.generators
            .binary_search_by_key(&constructor, |entry| entry.constructor)
            .ok()
            .map(|index| &self.generators[index])
    }

    /// Validate the exact finite rule/constructor premise needed by a
    /// product-inductive fold.  This rejects an opaque or literal-bearing
    /// `Grade = BigInt`: no finite constructor roster covers those values.
    pub fn check(
        selector: &FundingProjectionSelectorV2,
        projected: &ProjectedLanguageCoreV1,
        base: &TheorySemanticImageV1,
        cost: &CostImageV1,
        image: &ProjectedTheorySemanticImageV1,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<Self, FiniteGradeRosterErrorV2> {
        use FiniteGradeRosterErrorV2 as Error;
        let source: &LanguageCoreV1 = &projected.base;
        cost.validate(source, base, limits)
            .map_err(|_| Error::InvalidSource)?;
        let projection = selector
            .validate_declaration(projected)
            .map_err(|_| Error::InvalidSelector)?;
        let base_fingerprint = base.fingerprint().map_err(|_| Error::InvalidSource)?;
        let projected_fingerprint = projected
            .fingerprint()
            .map_err(|_| Error::InvalidSelector)?;
        if image.base_image_fingerprint != base_fingerprint
            || image.projected_language_fingerprint != projected_fingerprint
            || image.execution.language_fingerprint != projected_fingerprint
            || image.base_rule_count as usize != base.rules.len()
            || image.execution.abi != base.abi
            || image.execution.compiler_abi != base.compiler_abi
            || image.execution.primitive_substrate_abi != base.primitive_substrate_abi
            || image.execution.grammar_fingerprint != base.grammar_fingerprint
            || image.execution.theory_fingerprint != base.theory_fingerprint
            || image.execution.resource_profile != base.resource_profile
            || image.execution.rules.get(..base.rules.len()) != Some(base.rules.as_slice())
            || image.execution.sorts.get(..base.sorts.len()) != Some(base.sorts.as_slice())
            || image.execution.constructors.get(..base.constructors.len())
                != Some(base.constructors.as_slice())
            || image.execution.judgments != base.judgments
            || image.execution.judgment_rules != base.judgment_rules
            || image.execution.judgment_patterns != base.judgment_patterns
            || image.execution.actions.get(..base.actions.len()) != Some(base.actions.as_slice())
        {
            return Err(Error::ImageMismatch);
        }
        let grade_sort = cost.grade_sort;
        if !matches!(
            base.sorts.get(grade_sort.0 as usize).map(|sort| &sort.kind),
            Some(TheorySortKindImageV1::Syntax { literal: None })
        ) {
            return Err(Error::OpenGradeSort);
        }
        let unit = base
            .constructors
            .get(cost.unit_constructor.0 as usize)
            .ok_or(Error::InvalidUnit)?;
        if unit.codomain != grade_sort || !unit.domain.is_empty() {
            return Err(Error::InvalidUnit);
        }
        let product = base
            .constructors
            .get(cost.product_constructor.0 as usize)
            .ok_or(Error::InvalidProduct)?;
        if product.codomain != grade_sort || product.domain != [grade_sort, grade_sort] {
            return Err(Error::InvalidProduct);
        }
        let mut generators =
            BTreeMap::<TheoryConstructorId, Option<CheckedGradeGeneratorV2>>::new();
        for constructor in &base.constructors {
            if constructor.codomain == grade_sort
                && constructor.id != cost.unit_constructor
                && constructor.id != cost.product_constructor
            {
                if !constructor.domain.is_empty() {
                    return Err(Error::OpenGenerator);
                }
                generators.insert(constructor.id, None);
            }
        }
        // A grade-sort equation or directed rewrite could make an e-class
        // contain competing constructor trees. The finite structural fold has
        // no elected normal form; host commutativity is proved separately and
        // never inferred from a guest rewrite.
        for rule in &base.rules {
            let left = rule
                .terms
                .get(rule.left.0 as usize)
                .ok_or(Error::InvalidSource)?;
            let right = rule
                .terms
                .get(rule.right.0 as usize)
                .ok_or(Error::InvalidSource)?;
            if left.sort == grade_sort || right.sort == grade_sort {
                return Err(Error::GradeRewrite);
            }
        }
        for row in &cost.rules {
            let program = base
                .rules
                .get(row.program.0 as usize)
                .ok_or(Error::InvalidSource)?;
            let constructor = nullary_constructor(&program.terms, row.grade_term)
                .ok_or(Error::DynamicRuleGrade)?;
            if constructor != cost.unit_constructor && !generators.contains_key(&constructor) {
                return Err(Error::DynamicRuleGrade);
            }
        }
        let mut relations = image.relations.iter().filter(|relation| {
            relation.projection as usize == projection
                && relation.direction == ProjectionDirectionV1::GuestToHost
        });
        let relation = relations.next().ok_or(Error::InvalidSelector)?;
        if relations.next().is_some() || relation.input_sort != grade_sort {
            return Err(Error::InvalidSelector);
        }
        let ProjectionRelationBodyImageV1::Rules(entries) = &relation.body else {
            return Err(Error::UnexpectedProjectionRule);
        };
        for entry in entries {
            let program = image
                .execution
                .rules
                .get(entry.program.0 as usize)
                .ok_or(Error::UnexpectedProjectionRule)?;
            if program.disposition != TheoryRuleDispositionV1::Executable
                || program.origin != (TheoryRuleOriginV1::Rewrite { source: entry.program.0 })
                || !program.variables.is_empty()
                || !program.premises.is_empty()
                || !program.premise_roots.is_empty()
                || program
                    .terms
                    .get(program.left.0 as usize)
                    .map(|term| term.sort)
                    != Some(grade_sort)
                || program
                    .terms
                    .get(program.right.0 as usize)
                    .map(|term| term.sort)
                    != Some(relation.output_sort)
            {
                return Err(Error::OpenProjectionRule);
            }
            let constructor = nullary_constructor(&program.terms, program.left)
                .ok_or(Error::OpenProjectionRule)?;
            if !closed_constructor_template(&program.terms, program.right) {
                return Err(Error::OpenProjectionRule);
            }
            let Some(slot) = generators.get_mut(&constructor) else {
                return Err(Error::UnexpectedProjectionRule);
            };
            if slot.is_some() {
                return Err(Error::DuplicateGenerator);
            }
            *slot = Some(CheckedGradeGeneratorV2 {
                constructor,
                projection_program: entry.program,
                source_occurrence: entry.source_occurrence,
            });
        }
        let mut checked = Vec::new();
        checked
            .try_reserve_exact(generators.len())
            .map_err(|_| Error::LimitExceeded)?;
        for (_, entry) in generators {
            checked.push(entry.ok_or(Error::MissingGenerator)?);
        }
        Ok(Self {
            grade_sort,
            unit: cost.unit_constructor,
            product: cost.product_constructor,
            generators: checked,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TheoryImageTermNodeV1;

    #[test]
    fn nullary_generator_rejects_arguments_and_slots() {
        let constructor = TheoryConstructorId(3);
        let mut terms = vec![TheoryImageTermNodeV1 {
            sort: TheorySortId(0),
            form: TheoryImageTermFormV1::Apply {
                operator: TheoryImageOperatorV1::Constructor(constructor),
                arguments: vec![],
                slots: vec![],
                remainder: None,
                pathmap_mode: None,
            },
        }];
        assert_eq!(nullary_constructor(&terms, TheoryTermId(0)), Some(constructor));
        if let TheoryImageTermFormV1::Apply { arguments, .. } = &mut terms[0].form {
            arguments.push(TheoryTermId(0));
        }
        assert_eq!(nullary_constructor(&terms, TheoryTermId(0)), None);
    }

    #[test]
    fn closed_template_refuses_non_constructor_terms() {
        let terms = vec![
            TheoryImageTermNodeV1 {
                sort: TheorySortId(0),
                form: TheoryImageTermFormV1::Apply {
                    operator: TheoryImageOperatorV1::Constructor(TheoryConstructorId(1)),
                    arguments: vec![TheoryTermId(1)],
                    slots: vec![],
                    remainder: None,
                    pathmap_mode: None,
                },
            },
            TheoryImageTermNodeV1 {
                sort: TheorySortId(0),
                form: TheoryImageTermFormV1::Slot(crate::TheoryVariableId(0)),
            },
        ];
        assert!(!closed_constructor_template(&terms, TheoryTermId(0)));
    }

    #[test]
    fn closed_template_accepts_sharing_but_refuses_cycles() {
        let leaf = TheoryImageTermNodeV1 {
            sort: TheorySortId(0),
            form: TheoryImageTermFormV1::Apply {
                operator: TheoryImageOperatorV1::Constructor(TheoryConstructorId(1)),
                arguments: vec![],
                slots: vec![],
                remainder: None,
                pathmap_mode: None,
            },
        };
        let mut terms = vec![
            TheoryImageTermNodeV1 {
                sort: TheorySortId(0),
                form: TheoryImageTermFormV1::Apply {
                    operator: TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
                    arguments: vec![TheoryTermId(1), TheoryTermId(1)],
                    slots: vec![],
                    remainder: None,
                    pathmap_mode: None,
                },
            },
            leaf,
        ];
        assert!(closed_constructor_template(&terms, TheoryTermId(0)));
        if let TheoryImageTermFormV1::Apply { arguments, .. } = &mut terms[1].form {
            arguments.push(TheoryTermId(0));
        }
        assert!(!closed_constructor_template(&terms, TheoryTermId(0)));
    }

    #[test]
    fn closed_template_checks_deep_chains_iteratively() {
        let depth = 4096_u32;
        let mut terms = Vec::new();
        for index in 0..depth {
            terms.push(TheoryImageTermNodeV1 {
                sort: TheorySortId(0),
                form: TheoryImageTermFormV1::Apply {
                    operator: TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
                    arguments: if index == 0 {
                        Vec::new()
                    } else {
                        vec![TheoryTermId(index - 1)]
                    },
                    slots: Vec::new(),
                    remainder: None,
                    pathmap_mode: None,
                },
            });
        }
        assert!(closed_constructor_template(&terms, TheoryTermId(depth - 1)));
    }

    #[test]
    fn fixed_host_template_refuses_extra_process_or_signature_shape() {
        let proc_sort = TheorySortId(4);
        let sig_sort = TheorySortId(5);
        let nil = TheoryConstructorId(10);
        let hash = TheoryConstructorId(11);
        let signed = TheoryConstructorId(12);
        let apply = |sort, constructor, arguments| TheoryImageTermNodeV1 {
            sort,
            form: TheoryImageTermFormV1::Apply {
                operator: TheoryImageOperatorV1::Constructor(constructor),
                arguments,
                slots: Vec::new(),
                remainder: None,
                pathmap_mode: None,
            },
        };
        let mut terms = vec![
            apply(proc_sort, nil, Vec::new()),
            apply(proc_sort, nil, Vec::new()),
            apply(sig_sort, hash, vec![TheoryTermId(1)]),
            apply(proc_sort, signed, vec![TheoryTermId(0), TheoryTermId(2)]),
        ];
        let accepts = |terms: &[TheoryImageTermNodeV1]| {
            fixed_signed_nil_template(
                terms,
                TheoryTermId(3),
                proc_sort,
                sig_sort,
                signed,
                nil,
                hash,
            )
        };
        assert!(accepts(&terms));
        terms[0] = apply(proc_sort, TheoryConstructorId(13), Vec::new());
        assert!(!accepts(&terms), "a nonempty or effectful body cannot be certified");
        terms[0] = apply(proc_sort, nil, Vec::new());
        terms[2] = apply(sig_sort, hash, vec![TheoryTermId(1), TheoryTermId(1)]);
        assert!(!accepts(&terms), "the signature constructor is exact unary Hash");
        terms[2] = apply(sig_sort, hash, vec![TheoryTermId(1)]);
        terms[1] = apply(proc_sort, TheoryConstructorId(13), Vec::new());
        assert!(!accepts(&terms), "the certified lane is exactly Hash(Nil)");
    }
}
