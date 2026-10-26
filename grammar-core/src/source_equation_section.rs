//! Source-bound admission of the exact collapse-equation section profile.
//!
//! `SourceEquationSection.v` proves the admitted quotient has unique normal
//! forms. This module only recognizes its sufficient source schemas; execution
//! reuses the existing compiled-rule engine. An unsupported profile is not a
//! refutation of the theory's laws. No cost declaration, witness string, or
//! constructor spelling is treated as evidence.

use crate::source_equation_terms::SourceEquationTerms;
use crate::{
    LanguageCoreV1, TheoryConstructorId, TheoryImageAdmissionLimits, TheoryImageError,
    TheoryRuleArenaV1, TheoryRuleDirectionV1, TheorySemanticImageV1, TheorySortId, TheoryTermId,
    TheoryVariableId,
};

/// Resolved roles of one candidate section profile, not authority to execute it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceEquationSectionRolesV1 {
    pub sort: TheorySortId,
    pub zero: TheoryConstructorId,
    pub unit: TheoryConstructorId,
    pub alternative: TheoryConstructorId,
    pub product: TheoryConstructorId,
    pub closure: TheoryConstructorId,
}

/// The universally quantified source schemas proved by the section model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum SourceEquationSectionLawV1 {
    AltZeroLeft,
    AltZeroRight,
    AltIdempotent,
    ProductZeroLeft,
    ProductZeroRight,
    ProductUnitLeft,
    ProductUnitRight,
    ClosureZero,
    ClosureUnit,
    ClosureNested,
}

/// Inspectable coordinates in the retained source. Not a certificate by itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceEquationSectionWitnessV1 {
    pub equation: u32,
    pub direction: TheoryRuleDirectionV1,
    pub law: SourceEquationSectionLawV1,
    /// Absent only for the two constant closure equations.
    pub variable: Option<TheoryVariableId>,
}

/// An immutable borrow of the exact admitted source and base semantic image.
/// Only the source/image validator and complete roster check can mint this.
/// It proves neither a continued interaction cut nor native funding authority.
#[derive(Debug)]
pub struct VerifiedSourceEquationSectionV1<'a> {
    language: &'a LanguageCoreV1,
    semantic: &'a TheorySemanticImageV1,
    roles: SourceEquationSectionRolesV1,
    witnesses: Vec<SourceEquationSectionWitnessV1>,
}

impl<'a> VerifiedSourceEquationSectionV1<'a> {
    pub fn language(&self) -> &'a LanguageCoreV1 {
        self.language
    }

    pub fn semantic_image(&self) -> &'a TheorySemanticImageV1 {
        self.semantic
    }

    pub fn roles(&self) -> SourceEquationSectionRolesV1 {
        self.roles
    }

    /// All equations in source order, including redundant admitted schemas.
    pub fn witnesses(&self) -> &[SourceEquationSectionWitnessV1] {
        &self.witnesses
    }
}

impl TheorySemanticImageV1 {
    /// Check this sufficient equation profile against a fully validated owner.
    ///
    /// Invalid source/image pairs are errors. A valid but unsupported profile
    /// returns `Ok(None)`. Every equation must be an unconditional instance of
    /// a schema and every schema must occur. Reversal and duplicate schemas are
    /// permitted. Role arities describe these equations, not a global arity cap.
    pub fn check_source_equation_section<'a>(
        &'a self,
        language: &'a LanguageCoreV1,
        roles: SourceEquationSectionRolesV1,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<Option<VerifiedSourceEquationSectionV1<'a>>, TheoryImageError> {
        self.validate(language, limits)?;
        let Some(resolved) = ResolvedRoles::new(language, self, roles) else {
            return Ok(None);
        };
        let mut witnesses = Vec::new();
        witnesses
            .try_reserve_exact(language.theory.equations.len())
            .map_err(|_| TheoryImageError::Allocation)?;
        let mut coverage = 0_u16;
        for (index, equation) in language.theory.equations.iter().enumerate() {
            if !equation.arena.premises.is_empty() || !equation.arena.premise_roots.is_empty() {
                return Ok(None);
            }
            let recognized = [
                (TheoryRuleDirectionV1::Forward, equation.left, equation.right),
                (TheoryRuleDirectionV1::Reverse, equation.right, equation.left),
            ]
            .into_iter()
            .find_map(|(direction, left, right)| {
                resolved
                    .recognize(&equation.arena, left, right)
                    .map(|(law, variable)| (direction, law, variable))
            });
            let Some((direction, law, variable)) = recognized else {
                return Ok(None);
            };
            coverage |= 1_u16 << law as u8;
            witnesses.push(SourceEquationSectionWitnessV1 {
                equation: u32::try_from(index)
                    .map_err(|_| TheoryImageError::LimitExceeded("equations"))?,
                direction,
                law,
                variable,
            });
        }
        // Ten schema obligations; duplicate source rows cannot replace a law.
        if coverage != (1_u16 << 10) - 1 {
            return Ok(None);
        }
        Ok(Some(VerifiedSourceEquationSectionV1 {
            language,
            semantic: self,
            roles,
            witnesses,
        }))
    }
}

struct ResolvedRoles<'a> {
    terms: SourceEquationTerms<'a>,
    zero: &'a str,
    unit: &'a str,
    alternative: &'a str,
    product: &'a str,
    closure: &'a str,
}

impl<'a> ResolvedRoles<'a> {
    fn new(
        language: &'a LanguageCoreV1,
        semantic: &TheorySemanticImageV1,
        roles: SourceEquationSectionRolesV1,
    ) -> Option<Self> {
        let ids = [roles.zero, roles.unit, roles.alternative, roles.product, roles.closure];
        for (position, (id, arity)) in ids.into_iter().zip([0, 0, 2, 2, 1]).enumerate() {
            if ids[..position].contains(&id) {
                return None;
            }
            let constructor = semantic.constructors.get(id.0 as usize)?;
            if constructor.codomain != roles.sort
                || constructor.domain.len() != arity
                || constructor.domain.iter().any(|sort| *sort != roles.sort)
            {
                return None;
            }
        }
        let declarations = &language.theory.constructors;
        Some(Self {
            terms: SourceEquationTerms {
                sort: &language.theory.sorts.get(roles.sort.0 as usize)?.name,
            },
            zero: &declarations.get(roles.zero.0 as usize)?.name,
            unit: &declarations.get(roles.unit.0 as usize)?.name,
            alternative: &declarations.get(roles.alternative.0 as usize)?.name,
            product: &declarations.get(roles.product.0 as usize)?.name,
            closure: &declarations.get(roles.closure.0 as usize)?.name,
        })
    }

    fn constant(&self, arena: &TheoryRuleArenaV1, root: TheoryTermId, name: &str) -> bool {
        self.terms.constructor::<0>(arena, root, name).is_some()
    }

    fn recognize(
        &self,
        arena: &TheoryRuleArenaV1,
        left: TheoryTermId,
        right: TheoryTermId,
    ) -> Option<(SourceEquationSectionLawV1, Option<TheoryVariableId>)> {
        use SourceEquationSectionLawV1::*;
        if let Some([a, b]) = self.terms.constructor(arena, left, self.alternative) {
            let output = self.terms.variable(arena, right)?;
            let variables = [self.terms.variable(arena, a), self.terms.variable(arena, b)];
            let law = if self.constant(arena, a, self.zero) && variables[1] == Some(output) {
                AltZeroLeft
            } else if self.constant(arena, b, self.zero) && variables[0] == Some(output) {
                AltZeroRight
            } else if variables == [Some(output), Some(output)] {
                AltIdempotent
            } else {
                return None;
            };
            return Some((law, Some(output)));
        }
        if let Some([a, b]) = self.terms.constructor(arena, left, self.product) {
            for (constant, variable, zero_law, unit_law) in [
                (a, b, ProductZeroLeft, ProductUnitLeft),
                (b, a, ProductZeroRight, ProductUnitRight),
            ] {
                let Some(variable) = self.terms.variable(arena, variable) else {
                    continue;
                };
                if self.constant(arena, constant, self.zero)
                    && self.constant(arena, right, self.zero)
                {
                    return Some((zero_law, Some(variable)));
                }
                if self.constant(arena, constant, self.unit)
                    && self.terms.variable(arena, right) == Some(variable)
                {
                    return Some((unit_law, Some(variable)));
                }
            }
            return None;
        }
        let [argument] = self.terms.constructor(arena, left, self.closure)?;
        if self.constant(arena, right, self.unit) {
            if self.constant(arena, argument, self.zero) {
                return Some((ClosureZero, None));
            }
            if self.constant(arena, argument, self.unit) {
                return Some((ClosureUnit, None));
            }
            return None;
        }
        let [inner] = self.terms.constructor(arena, argument, self.closure)?;
        let [output] = self.terms.constructor(arena, right, self.closure)?;
        let variable = self.terms.variable(arena, inner)?;
        (self.terms.variable(arena, output)? == variable).then_some((ClosureNested, Some(variable)))
    }
}
