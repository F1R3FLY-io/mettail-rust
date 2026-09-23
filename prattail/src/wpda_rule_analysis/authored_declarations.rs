//! Borrow retained declarations through the original shared derivation workers.
//!
//! No source AST, lexer graph, classifier or synthetic rule is reconstructed.
//! Construction requires the existing Core and authored-reader checks and a
//! present header/binding pair. The original global token roster is distinct
//! from execution IDs and from the mode-local token rosters.
//!
//! `AuthoredDeclarationReaderProjection.v` covers these source observations and
//! worker substitutions. It does not establish runtime image/resource admission,
//! native decoder parity, synthetic-rule completeness or installed-parser use.

use super::authored::{AuthoredReaderError, AuthoredRuleReader};
use super::census::{collect_category_names_with_literals, CategoryCensusReader};
use super::native_first::{self, EmissionContext, LiteralFamily, NativeFirstConstructors};
use mettail_grammar_core::{
    AuthoredCategoryDeclaration, AuthoredDeclarationBindings, AuthoredDeclarations, AuthoredName,
    AuthoredNameId, AuthoredNode, AuthoredRuleId, AuthoredTokenBinding, AuthoredTokenDeclaration,
    CategoryId, GrammarCoreV1, ModeId, NativeKind, ValidationError,
};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthoredDeclarationReaderError {
    MissingStore,
    MissingDeclarations,
    MissingBindings,
    InvalidCore(Vec<ValidationError>),
    InvalidRule(AuthoredRuleId),
    RuleReader(AuthoredReaderError),
}

impl fmt::Display for AuthoredDeclarationReaderError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingStore => formatter.write_str("authored rule store is unavailable"),
            Self::MissingDeclarations => {
                formatter.write_str("authored declarations are unavailable")
            },
            Self::MissingBindings => {
                formatter.write_str("authored declaration bindings are unavailable")
            },
            Self::InvalidCore(errors) => write!(formatter, "invalid declaration Core: {errors:?}"),
            Self::InvalidRule(rule) => {
                write!(formatter, "authored rule {} is not a Rule node", rule.0)
            },
            Self::RuleReader(error) => write!(formatter, "{error}"),
        }
    }
}

impl std::error::Error for AuthoredDeclarationReaderError {}

/// Validated immutable source views, not installed language authority.
pub struct AuthoredDeclarationReader<'core> {
    rules: AuthoredRuleReader<'core>,
    header: &'core AuthoredDeclarations,
    bindings: &'core AuthoredDeclarationBindings,
    core: &'core GrammarCoreV1,
}

impl<'core> AuthoredDeclarationReader<'core> {
    pub fn new(core: &'core GrammarCoreV1) -> Result<Self, AuthoredDeclarationReaderError> {
        let store = core
            .authored
            .as_ref()
            .ok_or(AuthoredDeclarationReaderError::MissingStore)?;
        let header = store
            .declarations()
            .ok_or(AuthoredDeclarationReaderError::MissingDeclarations)?;
        let bindings = core
            .authored_bindings
            .as_ref()
            .ok_or(AuthoredDeclarationReaderError::MissingBindings)?;
        core.validate()
            .map_err(AuthoredDeclarationReaderError::InvalidCore)?;
        let rules =
            AuthoredRuleReader::new(store).map_err(AuthoredDeclarationReaderError::RuleReader)?;
        Ok(Self { rules, header, bindings, core })
    }

    pub fn header(&self) -> &'core AuthoredDeclarations {
        self.header
    }

    pub fn rule_reader(&self) -> &AuthoredRuleReader<'core> {
        &self.rules
    }

    fn name(&self, id: AuthoredNameId) -> &'core AuthoredName {
        self.rules.name(id).payload()
    }

    fn token(&self, index: u32) -> &'core AuthoredTokenDeclaration {
        self.header
            .tokens
            .get(index as usize)
            .expect("source token index belongs to validated header roster")
    }

    /// Preserve the caller's original rule order and duplicates. Validate every
    /// supplied handle before the original worker performs any classification.
    /// Generated/synthetic rules must not be inserted into this source roster.
    pub fn collect_category_names(
        &mut self,
        rules: &[AuthoredRuleId],
    ) -> Result<Vec<String>, AuthoredDeclarationReaderError> {
        let store = self
            .core
            .authored
            .as_ref()
            .expect("reader construction checked store presence");
        for rule in rules {
            if !matches!(store.get(rule.0), Some(AuthoredNode::Rule(_))) {
                return Err(AuthoredDeclarationReaderError::InvalidRule(*rule));
            }
        }
        let header = self.header;
        Ok(collect_category_names_with_literals(
            rules,
            &header.categories,
            &header.global_tokens,
            self,
        ))
    }

    /// Return a source token position, never a guessed final lexer ID.
    pub fn declared_literal(&self, category: &str) -> Option<&'core u32> {
        native_first::declared_literal_token_def(
            category,
            &self.header.global_tokens,
            |index| self.token(*index).from_literals,
            |index| self.token(*index).has_evaluation,
            |index| {
                self.token(*index)
                    .category
                    .map(|id| self.name(id).spelling.clone())
            },
        )
    }

    pub fn literal_family(&self, category: &str) -> Option<LiteralFamily> {
        native_first::literal_family_for_category(
            category,
            &self.header.categories,
            |row| self.name(row.name).spelling.clone(),
            |row| row.native.as_ref(),
            |kind| *kind,
            |name| self.declared_literal(name).is_some(),
        )
    }

    /// Delegate constructor calls at their original sites, including the
    /// discarded first home Integer arm. No new pattern vocabulary is created.
    pub fn native_rows<C: NativeFirstConstructors>(
        &self,
        category: &str,
        family: LiteralFamily,
        kind: Option<&NativeKind>,
        context: EmissionContext,
        constructors: &mut C,
    ) -> Vec<(C::Pattern, Option<C::Pattern>)> {
        native_first::literal_patterned_pattern_and_guard_for_kind(
            category,
            family,
            kind,
            context,
            constructors,
        )
    }

    pub fn guest_nested_open_kinds(&self, open: &str) -> Vec<String> {
        super::guest::guest_body_nested_open_kinds(
            &self.header.global_tokens,
            &self.header.modes,
            open,
            |index, open| self.name(self.token(*index).name).spelling == open,
            |index| {
                self.token(*index)
                    .push
                    .map(|id| &self.name(id).equality_class)
            },
            |mode| &self.name(mode.name).equality_class,
            |mode| &mode.tokens,
            |index| self.name(self.token(*index).name).spelling.clone(),
        )
    }

    pub fn category_binding(&self, index: usize) -> Option<&'core CategoryId> {
        self.bindings.categories.get(index)
    }

    pub fn token_binding(&self, index: usize) -> Option<&'core AuthoredTokenBinding> {
        self.bindings.tokens.get(index)
    }

    pub fn mode_binding(&self, index: usize) -> Option<&'core ModeId> {
        self.bindings.modes.get(index)
    }

    /// Reuse the existing producer relation `admits_variables = !is_data`.
    /// A missing source row is not guessed to be either role.
    pub fn is_data(&self, index: usize) -> Option<bool> {
        let target = self.category_binding(index)?;
        self.core
            .categories
            .get(target.0 as usize)
            .map(|category| !category.admits_variables)
    }
}

/// Low-level callbacks require handles/rows from this reader's validated store,
/// as do the existing AuthoredRuleReader traits. Use collect_category_names to
/// check an external rule-ID slice before dispatching the census.
impl CategoryCensusReader for AuthoredDeclarationReader<'_> {
    type Rule = AuthoredRuleId;
    type Type = AuthoredCategoryDeclaration;
    type Token = u32;

    fn rule_category(&mut self, rule: &Self::Rule) -> String {
        self.name(self.rules.rule(*rule).category).spelling.clone()
    }
    fn type_name(&mut self, category: &Self::Type) -> String {
        self.name(category.name).spelling.clone()
    }
    fn has_collection(&mut self, category: &Self::Type) -> bool {
        category.collection.is_some()
    }
    fn has_native(&mut self, category: &Self::Type) -> bool {
        category.native.is_some()
    }
    fn from_literals(&mut self, token: &Self::Token) -> bool {
        self.token(*token).from_literals
    }
    fn token_category(&mut self, token: &Self::Token) -> Option<String> {
        self.token(*token)
            .category
            .map(|id| self.name(id).spelling.clone())
    }
}

#[cfg(test)]
mod tests;
