//! Retained observations for the original patterned-literal eligibility helper.
//! This prefix-only consumer observes evaluation presence, not its payload.
//! Decoder/evaluator provenance remains in existing Core token bindings; these
//! bucket rows neither carry nor grant evaluation authority.

use super::super::authored::{AuthoredNameRef, AuthoredRuleReader};
use super::super::authored_declarations::AuthoredDeclarationReader;
use super::super::binder::rule::BinderRuleReader;
use super::super::native_first::{
    literal_patterned_pattern_and_guard_for_kind, EmissionContext, LiteralFamily,
};
use super::super::native_literal::{
    try_classify_literal_patterned, LiteralPatternedPayload, LiteralPatternedReader,
};
use super::super::prefix_pattern::{NeutralNativeFirstConstructors, NeutralPattern};
use mettail_grammar_core::constructor_labels::try_generate_literal_label_observed;
use mettail_grammar_core::{
    AuthoredCategoryDeclaration, AuthoredNameId, NativeKind, SourceObservation,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LiteralError {
    UnavailableByteObservation,
    UnavailableNativeObservation,
    AbsentNativeObservation,
}

pub(super) type OwnedLiteral<'source> =
    LiteralPatternedPayload<&'source AuthoredCategoryDeclaration, String, ()>;

impl OwnedLiteral<'_> {
    pub(super) fn rows(
        &self,
        mode: EmissionContext,
    ) -> Vec<(NeutralPattern, Option<NeutralPattern>)> {
        literal_patterned_pattern_and_guard_for_kind(
            &self.cat_name,
            self.family,
            self.native_type.native.as_ref(),
            mode,
            &mut NeutralNativeFirstConstructors,
        )
    }
}

struct Reader<'borrow, 'source> {
    rules: &'borrow AuthoredRuleReader<'source>,
    declarations: &'borrow AuthoredDeclarationReader<'source>,
}

impl<'source> LiteralPatternedReader<'source> for Reader<'_, 'source> {
    type Name = AuthoredNameRef<'source>;
    type Category = AuthoredCategoryDeclaration;
    type Native = &'source AuthoredCategoryDeclaration;
    type Label = String;
    type Evaluation = ();
    type Token = u32;
    type Error = LiteralError;

    fn categories(&self) -> &'source [Self::Category] {
        &self.declarations.header().categories
    }
    fn category_name(&self, category: &'source Self::Category) -> Self::Name {
        self.rules.name(category.name)
    }
    fn names_equal(&self, left: Self::Name, right: Self::Name) -> bool {
        self.rules.names_equal(left, right)
    }
    fn native_type(&self, category: &'source Self::Category) -> Option<Self::Native> {
        category.native.as_ref().map(|_| category)
    }
    fn native_kind(&self, native: &Self::Native) -> NativeKind {
        native
            .native
            .expect("original native-presence gate returned this declaration")
    }
    fn literal_family(&self, category: &str) -> Option<LiteralFamily> {
        self.declarations.literal_family(category)
    }
    fn literal_label(&mut self, native: &Self::Native) -> Result<String, LiteralError> {
        try_generate_literal_label_observed(
            || match native.byte_observation {
                SourceObservation::Known(value) => Ok(value),
                SourceObservation::Unavailable => Err(LiteralError::UnavailableByteObservation),
            },
            || match &native.literal_observation {
                SourceObservation::Known(Some(value)) => Ok(value.clone()),
                SourceObservation::Known(None) => Err(LiteralError::AbsentNativeObservation),
                SourceObservation::Unavailable => Err(LiteralError::UnavailableNativeObservation),
            },
            |label| Ok(label.to_owned()),
        )
    }
    fn declared_token(&self, category: &str) -> Option<u32> {
        self.declarations.declared_literal(category).copied()
    }
    fn evaluation(&self, token: u32) -> Option<()> {
        self.declarations.header().tokens[token as usize]
            .has_evaluation
            .then_some(())
    }
    fn default_evaluation(&self, kind: &NativeKind) -> Option<()> {
        // The original default_eval_body_for_native_kind has a body for every
        // listed builtin and refuses Other. This retains that source eligibility
        // only; it does not supply or execute another evaluator.
        match kind {
            NativeKind::Other => None,
            NativeKind::Int8
            | NativeKind::Int16
            | NativeKind::Int32
            | NativeKind::Int64
            | NativeKind::Int128
            | NativeKind::Isize
            | NativeKind::UInt8
            | NativeKind::UInt16
            | NativeKind::UInt32
            | NativeKind::UInt64
            | NativeKind::UInt128
            | NativeKind::Usize
            | NativeKind::CanonicalBigInt
            | NativeKind::CanonicalBigRat
            | NativeKind::CanonicalFixedPoint
            | NativeKind::Float32
            | NativeKind::Float64
            | NativeKind::Bool
            | NativeKind::Str => Some(()),
        }
    }
}

pub(super) fn resolve<'source>(
    rules: &AuthoredRuleReader<'source>,
    declarations: &AuthoredDeclarationReader<'source>,
    name: AuthoredNameId,
) -> Result<Option<OwnedLiteral<'source>>, LiteralError> {
    try_classify_literal_patterned(rules.name(name), &mut Reader { rules, declarations })
}
