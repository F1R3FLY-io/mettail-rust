//! Sufficient ACU evidence from the checked owner's actual source equations.
//!
//! This is the fixed-schema admission check modeled by
//! `SourceSignatureMonoidAdmission.v`, not an equation solver. Recognition
//! borrows arena nodes at fixed schema positions; it neither allocates nor
//! traverses arbitrary-depth terms. Substituted values remain unrestricted.

use super::VerifiedCostImageV1;
use crate::source_equation_terms::SourceEquationTerms;
use crate::{
    TheoryEquationV1, TheoryRuleArenaV1, TheoryRuleDirectionV1, TheoryTermId, TheoryVariableId,
};

/// Universally quantified signature-law schema and its source variable IDs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceSignatureLawV1 {
    Associativity { variables: [TheoryVariableId; 3] },
    Commutativity { variables: [TheoryVariableId; 2] },
    LeftUnit { variable: TheoryVariableId },
    RightUnit { variable: TheoryVariableId },
}

/// Inspectable evidence coordinates. These values alone cannot mint a
/// `VerifiedSourceSignatureAcuV1` or authorize native funding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceSignatureLawWitnessV1 {
    pub equation: u32,
    pub direction: TheoryRuleDirectionV1,
    pub law: SourceSignatureLawV1,
}

/// Source-bound associativity, commutativity, and unit evidence. A unit on
/// either side suffices because commutativity establishes the other side.
/// This certificate does not establish a section, faithfulness, or Cost(G).
#[derive(Clone, Copy, Debug)]
pub struct VerifiedSourceSignatureAcuV1<'a> {
    cost_image: VerifiedCostImageV1<'a>,
    associativity: SourceSignatureLawWitnessV1,
    commutativity: SourceSignatureLawWitnessV1,
    unit: SourceSignatureLawWitnessV1,
}

impl<'a> VerifiedSourceSignatureAcuV1<'a> {
    pub fn cost_image(&self) -> VerifiedCostImageV1<'a> {
        self.cost_image
    }

    pub fn associativity(&self) -> SourceSignatureLawWitnessV1 {
        self.associativity
    }

    pub fn commutativity(&self) -> SourceSignatureLawWitnessV1 {
        self.commutativity
    }

    pub fn unit(&self) -> SourceSignatureLawWitnessV1 {
        self.unit
    }
}

impl<'a> VerifiedCostImageV1<'a> {
    /// Recognize unconditional ACU schemas in this image's authored equations.
    /// `None` means uncertified by this sufficient check, not a refuted law.
    /// Ordinary cost-image admission and legacy witness strings are unchanged.
    pub fn check_source_signature_acu(&self) -> Option<VerifiedSourceSignatureAcuV1<'a>> {
        let theory = &self.language.theory;
        let roles = SignatureRoles {
            sort: &theory.sorts.get(self.grade_sort().0 as usize)?.name,
            unit: &theory
                .constructors
                .get(self.unit_constructor().0 as usize)?
                .name,
            product: &theory
                .constructors
                .get(self.product_constructor().0 as usize)?
                .name,
        };
        Some(VerifiedSourceSignatureAcuV1 {
            cost_image: *self,
            associativity: roles.find(&theory.equations, Obligation::Associativity)?,
            commutativity: roles.find(&theory.equations, Obligation::Commutativity)?,
            unit: roles.find(&theory.equations, Obligation::Unit)?,
        })
    }
}

#[derive(Clone, Copy)]
enum Obligation {
    Associativity,
    Commutativity,
    Unit,
}

struct SignatureRoles<'a> {
    sort: &'a str,
    unit: &'a str,
    product: &'a str,
}

impl SignatureRoles<'_> {
    fn find(
        &self,
        equations: &[TheoryEquationV1],
        obligation: Obligation,
    ) -> Option<SourceSignatureLawWitnessV1> {
        for (index, equation) in equations.iter().enumerate() {
            if !equation.arena.premises.is_empty() || !equation.arena.premise_roots.is_empty() {
                continue;
            }
            for (direction, left, right) in [
                (TheoryRuleDirectionV1::Forward, equation.left, equation.right),
                (TheoryRuleDirectionV1::Reverse, equation.right, equation.left),
            ] {
                if let Some(law) = self.recognize(&equation.arena, obligation, left, right) {
                    return Some(SourceSignatureLawWitnessV1 {
                        equation: u32::try_from(index).ok()?,
                        direction,
                        law,
                    });
                }
            }
        }
        None
    }

    fn variable(&self, arena: &TheoryRuleArenaV1, root: TheoryTermId) -> Option<TheoryVariableId> {
        SourceEquationTerms { sort: self.sort }.variable(arena, root)
    }

    fn product(&self, arena: &TheoryRuleArenaV1, root: TheoryTermId) -> Option<[TheoryTermId; 2]> {
        SourceEquationTerms { sort: self.sort }.constructor(arena, root, self.product)
    }

    fn is_unit(&self, arena: &TheoryRuleArenaV1, root: TheoryTermId) -> bool {
        SourceEquationTerms { sort: self.sort }
            .constructor::<0>(arena, root, self.unit)
            .is_some()
    }

    fn recognize(
        &self,
        arena: &TheoryRuleArenaV1,
        obligation: Obligation,
        left: TheoryTermId,
        right: TheoryTermId,
    ) -> Option<SourceSignatureLawV1> {
        let [a, b] = self.product(arena, left)?;
        match obligation {
            Obligation::Associativity => {
                let [x, y] = self.product(arena, a)?;
                let [x, y, z] =
                    [self.variable(arena, x)?, self.variable(arena, y)?, self.variable(arena, b)?];
                if x == y || x == z || y == z {
                    return None;
                }
                let [rx, ryz] = self.product(arena, right)?;
                let [ry, rz] = self.product(arena, ryz)?;
                (self.variable(arena, rx)? == x
                    && self.variable(arena, ry)? == y
                    && self.variable(arena, rz)? == z)
                    .then_some(SourceSignatureLawV1::Associativity { variables: [x, y, z] })
            },
            Obligation::Commutativity => {
                let [x, y] = [self.variable(arena, a)?, self.variable(arena, b)?];
                if x == y {
                    return None;
                }
                let [ry, rx] = self.product(arena, right)?;
                (self.variable(arena, ry)? == y && self.variable(arena, rx)? == x)
                    .then_some(SourceSignatureLawV1::Commutativity { variables: [x, y] })
            },
            Obligation::Unit => {
                let variable = self.variable(arena, right)?;
                if self.is_unit(arena, a) && self.variable(arena, b) == Some(variable) {
                    Some(SourceSignatureLawV1::LeftUnit { variable })
                } else if self.variable(arena, a) == Some(variable) && self.is_unit(arena, b) {
                    Some(SourceSignatureLawV1::RightUnit { variable })
                } else {
                    None
                }
            },
        }
    }
}
