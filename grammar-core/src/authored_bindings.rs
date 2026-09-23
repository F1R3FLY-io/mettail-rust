//! Final-ID associations for immutable retained source declarations.
//!
//! Frontends record IDs at their existing append/coalescing sites. Validation
//! checks structural associations, not decoder or native-value equivalence.
//! `AuthoredDeclarationBindingProjection.v` models these phase boundaries.

use crate::{
    AuthoredDeclarations, AuthoredNode, AuthoredRuleStore, CategoryId, GrammarCoreV1, ModeId,
    TokenId,
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthoredTokenBinding {
    pub direct: TokenId,
    #[serde(deserialize_with = "crate::core::required_option")]
    pub typed_literal: Option<TokenId>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthoredDeclarationBindings {
    pub categories: Vec<CategoryId>,
    pub tokens: Vec<AuthoredTokenBinding>,
    pub modes: Vec<ModeId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthoredBindingError {
    PresenceMismatch,
    CountMismatch {
        field: &'static str,
        expected: usize,
        actual: usize,
    },
    IndexOverflow {
        field: &'static str,
    },
    AllocationRefused {
        field: &'static str,
    },
    SourceIndexOutOfBounds {
        field: &'static str,
        index: usize,
    },
    AlreadyBound {
        field: &'static str,
        index: usize,
    },
    Unfinished {
        field: &'static str,
        index: usize,
    },
    InvalidTarget {
        field: &'static str,
        index: usize,
        target: u32,
    },
    CategorySpelling {
        index: usize,
        target: u32,
    },
    TokenMode {
        index: usize,
        token: u32,
        expected: u32,
    },
    TokenMembership {
        index: usize,
        token: u32,
        mode: u32,
    },
}

impl std::fmt::Display for AuthoredBindingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PresenceMismatch => {
                write!(f, "authored declarations and bindings must both be present or absent")
            },
            Self::CountMismatch { field, expected, actual } => write!(
                f,
                "authored {field} binding count {actual} differs from source count {expected}"
            ),
            Self::IndexOverflow { field } => write!(f, "authored {field} count exceeds u32"),
            Self::AllocationRefused { field } => {
                write!(f, "cannot reserve authored {field} bindings")
            },
            Self::SourceIndexOutOfBounds { field, index } => {
                write!(f, "authored {field} source index {index} is out of bounds")
            },
            Self::AlreadyBound { field, index } => {
                write!(f, "authored {field} source index {index} is already bound")
            },
            Self::Unfinished { field, index } => {
                write!(f, "authored {field} source index {index} has not been bound")
            },
            Self::InvalidTarget { field, index, target } => {
                write!(f, "authored {field} source index {index} has invalid target {target}")
            },
            Self::CategorySpelling { index, target } => {
                write!(f, "authored category {index} spelling differs from Core category {target}")
            },
            Self::TokenMode { index, token, expected } => {
                write!(f, "authored token {index} target {token} is not in mode {expected}")
            },
            Self::TokenMembership { index, token, mode } => write!(
                f,
                "authored token {index} target {token} is absent from mode {mode}'s roster"
            ),
        }
    }
}

impl std::error::Error for AuthoredBindingError {}

/// Private pending slots cannot be serialized or exposed as a completed table.
/// Callers admit source-roster storage before constructing this builder.
#[derive(Debug)]
pub struct AuthoredDeclarationBindingsBuilder {
    categories: Vec<Option<CategoryId>>,
    direct: Vec<Option<TokenId>>,
    // None is unfinished; Some(None) explicitly records no auxiliary route.
    typed_literal: Vec<Option<Option<TokenId>>>,
    modes: Vec<Option<ModeId>>,
}

fn slots<T>(count: usize, field: &'static str) -> Result<Vec<Option<T>>, AuthoredBindingError> {
    u32::try_from(count).map_err(|_| AuthoredBindingError::IndexOverflow { field })?;
    let mut slots = Vec::new();
    slots
        .try_reserve_exact(count)
        .map_err(|_| AuthoredBindingError::AllocationRefused { field })?;
    slots.resize_with(count, || None);
    Ok(slots)
}

fn bind_once<T>(
    slots: &mut [Option<T>],
    index: usize,
    value: T,
    field: &'static str,
) -> Result<(), AuthoredBindingError> {
    let slot = slots
        .get_mut(index)
        .ok_or(AuthoredBindingError::SourceIndexOutOfBounds { field, index })?;
    if slot.is_some() {
        return Err(AuthoredBindingError::AlreadyBound { field, index });
    }
    *slot = Some(value);
    Ok(())
}

fn count_matches(
    actual: usize,
    expected: usize,
    field: &'static str,
) -> Result<(), AuthoredBindingError> {
    if actual != expected {
        return Err(AuthoredBindingError::CountMismatch { field, expected, actual });
    }
    Ok(())
}

fn finish_slots<T>(
    slots: Vec<Option<T>>,
    field: &'static str,
) -> Result<Vec<T>, AuthoredBindingError> {
    let mut output = Vec::new();
    output
        .try_reserve_exact(slots.len())
        .map_err(|_| AuthoredBindingError::AllocationRefused { field })?;
    for (index, slot) in slots.into_iter().enumerate() {
        output.push(slot.ok_or(AuthoredBindingError::Unfinished { field, index })?);
    }
    Ok(output)
}

impl AuthoredDeclarationBindingsBuilder {
    pub fn try_new(header: &AuthoredDeclarations) -> Result<Self, AuthoredBindingError> {
        Ok(Self {
            categories: slots(header.categories.len(), "categories")?,
            direct: slots(header.tokens.len(), "direct tokens")?,
            typed_literal: slots(header.tokens.len(), "typed literal tokens")?,
            modes: slots(header.modes.len(), "modes")?,
        })
    }

    pub fn bind_category(
        &mut self,
        index: usize,
        target: CategoryId,
    ) -> Result<(), AuthoredBindingError> {
        bind_once(&mut self.categories, index, target, "categories")
    }

    pub fn bind_token_direct(
        &mut self,
        index: usize,
        target: TokenId,
    ) -> Result<(), AuthoredBindingError> {
        bind_once(&mut self.direct, index, target, "direct tokens")
    }

    pub fn bind_token_typed_literal(
        &mut self,
        index: usize,
        target: Option<TokenId>,
    ) -> Result<(), AuthoredBindingError> {
        bind_once(&mut self.typed_literal, index, target, "typed literal tokens")
    }

    pub fn bind_mode(&mut self, index: usize, target: ModeId) -> Result<(), AuthoredBindingError> {
        bind_once(&mut self.modes, index, target, "modes")
    }

    /// Finalize completeness only. The enclosing Core must validate final IDs
    /// against its immutable store and execution rosters before publication.
    pub fn finish(
        self,
        header: &AuthoredDeclarations,
    ) -> Result<AuthoredDeclarationBindings, AuthoredBindingError> {
        let categories = finish_slots(self.categories, "categories")?;
        let direct = finish_slots(self.direct, "direct tokens")?;
        let typed_literal = finish_slots(self.typed_literal, "typed literal tokens")?;
        let modes = finish_slots(self.modes, "modes")?;
        count_matches(categories.len(), header.categories.len(), "categories")?;
        count_matches(direct.len(), header.tokens.len(), "direct tokens")?;
        count_matches(typed_literal.len(), header.tokens.len(), "typed literal tokens")?;
        count_matches(modes.len(), header.modes.len(), "modes")?;
        let mut tokens = Vec::new();
        tokens
            .try_reserve_exact(direct.len())
            .map_err(|_| AuthoredBindingError::AllocationRefused { field: "tokens" })?;
        for (direct, typed_literal) in direct.into_iter().zip(typed_literal) {
            tokens.push(AuthoredTokenBinding { direct, typed_literal });
        }
        Ok(AuthoredDeclarationBindings { categories, tokens, modes })
    }
}

impl AuthoredDeclarationBindings {
    pub fn validate(
        &self,
        store: &AuthoredRuleStore,
        core: &GrammarCoreV1,
    ) -> Result<(), AuthoredBindingError> {
        let header = store
            .declarations()
            .ok_or(AuthoredBindingError::PresenceMismatch)?;
        count_matches(self.categories.len(), header.categories.len(), "categories")?;
        count_matches(self.tokens.len(), header.tokens.len(), "tokens")?;
        count_matches(self.modes.len(), header.modes.len(), "modes")?;
        for (index, (source, target)) in header.categories.iter().zip(&self.categories).enumerate()
        {
            let Some(AuthoredNode::Name(name)) = store.get(source.name.0) else {
                return Err(AuthoredBindingError::InvalidTarget {
                    field: "source category name",
                    index,
                    target: source.name.0,
                });
            };
            let category = core.categories.get(target.0 as usize).ok_or(
                AuthoredBindingError::InvalidTarget {
                    field: "categories",
                    index,
                    target: target.0,
                },
            )?;
            if name.spelling != category.name {
                return Err(AuthoredBindingError::CategorySpelling { index, target: target.0 });
            }
        }
        for &index in &header.global_tokens {
            self.validate_token(core, index as usize, ModeId(0))?;
        }
        for (index, (source, &target)) in header.modes.iter().zip(&self.modes).enumerate() {
            core.modes
                .get(target.0 as usize)
                .ok_or(AuthoredBindingError::InvalidTarget {
                    field: "modes",
                    index,
                    target: target.0,
                })?;
            for &source_index in &source.tokens {
                self.validate_token(core, source_index as usize, target)?;
            }
        }
        Ok(())
    }

    fn validate_token(
        &self,
        core: &GrammarCoreV1,
        index: usize,
        expected: ModeId,
    ) -> Result<(), AuthoredBindingError> {
        let binding = self
            .tokens
            .get(index)
            .ok_or(AuthoredBindingError::SourceIndexOutOfBounds { field: "tokens", index })?;
        self.validate_route(core, index, binding.direct, expected)?;
        if let Some(auxiliary) = binding.typed_literal {
            self.validate_route(core, index, auxiliary, expected)?;
        }
        Ok(())
    }

    fn validate_route(
        &self,
        core: &GrammarCoreV1,
        index: usize,
        target: TokenId,
        expected: ModeId,
    ) -> Result<(), AuthoredBindingError> {
        let token =
            core.tokens
                .get(target.0 as usize)
                .ok_or(AuthoredBindingError::InvalidTarget {
                    field: "tokens",
                    index,
                    target: target.0,
                })?;
        let mode =
            core.modes
                .get(expected.0 as usize)
                .ok_or(AuthoredBindingError::InvalidTarget {
                    field: "token mode",
                    index,
                    target: expected.0,
                })?;
        if token.mode != expected {
            return Err(AuthoredBindingError::TokenMode {
                index,
                token: target.0,
                expected: expected.0,
            });
        }
        if !mode.token_ids.contains(&target) {
            return Err(AuthoredBindingError::TokenMembership {
                index,
                token: target.0,
                mode: expected.0,
            });
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        AuthoredCategoryDeclaration, AuthoredModeDeclaration, AuthoredName, AuthoredNameId,
        AuthoredTokenDeclaration, Carrier, Category, LexerMode, ModeTransition, NativeKind,
        Reservation, TokenDecoder, TokenDefinition, TokenPattern, ValidationError,
        GRAMMAR_CORE_ABI_V3, GRAMMAR_CORE_ABI_V4,
    };

    fn fixture() -> GrammarCoreV1 {
        let mut store = AuthoredRuleStore::new();
        let mut name = |spelling: &str, equality_class| {
            AuthoredNameId(
                store
                    .try_push(AuthoredNode::Name(AuthoredName {
                        spelling: spelling.into(),
                        equality_class,
                    }))
                    .expect("fixture name must append to the flat arena"),
            )
        };
        let category = name("Expr", 0);
        let token = name("SourceName", 1);
        let mode = name("Quoted", 2);
        let row = AuthoredTokenDeclaration {
            name: token,
            category: Some(category),
            from_literals: true,
            has_evaluation: true,
            push: None,
        };
        let header = AuthoredDeclarations {
            categories: vec![AuthoredCategoryDeclaration {
                name: category,
                native: Some(NativeKind::Other),
                collection: None,
            }],
            tokens: vec![row.clone(), row.clone(), row],
            global_tokens: vec![0, 1],
            modes: vec![AuthoredModeDeclaration { name: mode, tokens: vec![2] }],
        };
        let mut core = GrammarCoreV1::new("bindings");
        core.categories.push(Category {
            id: CategoryId(0),
            name: "Expr".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: true,
        });
        core.modes[0].token_ids = vec![TokenId(0), TokenId(1)];
        core.modes.push(LexerMode {
            id: ModeId(1),
            name: "Quoted".into(),
            token_ids: vec![TokenId(2)],
            raw: false,
        });
        for (index, mode) in [ModeId(0), ModeId(0), ModeId(1)].into_iter().enumerate() {
            core.tokens.push(TokenDefinition {
                id: TokenId(index as u32),
                name: format!("qualified/execution/{index}"),
                pattern: TokenPattern::Literal(format!("token{index}")),
                // Macro execution tokens need not duplicate authored metadata.
                category: None,
                evaluation: None,
                priority: 0,
                mode,
                channel: "main".into(),
                transition: ModeTransition::default(),
                decoder: TokenDecoder::Unit,
                reservation: Reservation::Contextual,
            });
        }
        core.authored = Some(
            store
                .with_declarations(header)
                .expect("fixture header references and source roster must validate"),
        );
        core.authored_bindings = Some(AuthoredDeclarationBindings {
            categories: vec![CategoryId(0)],
            tokens: vec![
                AuthoredTokenBinding {
                    direct: TokenId(0),
                    typed_literal: Some(TokenId(1)),
                },
                AuthoredTokenBinding { direct: TokenId(0), typed_literal: None },
                AuthoredTokenBinding { direct: TokenId(2), typed_literal: None },
            ],
            modes: vec![ModeId(1)],
        });
        core
    }

    fn table(core: &GrammarCoreV1) -> &AuthoredDeclarationBindings {
        core.authored_bindings
            .as_ref()
            .expect("fixture retains a binding table")
    }
    fn store(core: &GrammarCoreV1) -> &AuthoredRuleStore {
        core.authored
            .as_ref()
            .expect("fixture retains its immutable store")
    }
    fn header(core: &GrammarCoreV1) -> &AuthoredDeclarations {
        store(core)
            .declarations()
            .expect("fixture retains source declarations")
    }

    #[test]
    fn authored_binding_builder_is_write_once_and_keeps_order() {
        let core = fixture();
        let mut builder = AuthoredDeclarationBindingsBuilder::try_new(header(&core))
            .expect("admitted fixture slots should reserve");
        builder
            .bind_token_direct(2, TokenId(2))
            .expect("out-of-order source assignment is allowed");
        assert_eq!(
            builder.bind_token_direct(2, TokenId(2)),
            Err(AuthoredBindingError::AlreadyBound { field: "direct tokens", index: 2 })
        );
        assert_eq!(
            builder.bind_token_direct(3, TokenId(9)),
            Err(AuthoredBindingError::SourceIndexOutOfBounds { field: "direct tokens", index: 3 })
        );
        builder
            .bind_category(0, CategoryId(0))
            .expect("category assignment succeeds");
        builder
            .bind_mode(0, ModeId(1))
            .expect("mode assignment succeeds");
        builder
            .bind_token_direct(0, TokenId(0))
            .expect("first global token assignment succeeds");
        builder
            .bind_token_direct(1, TokenId(0))
            .expect("coalesced global token assignment succeeds");
        for (index, auxiliary) in [Some(TokenId(1)), None, None].into_iter().enumerate() {
            builder
                .bind_token_typed_literal(index, auxiliary)
                .expect("every optional route must be finalized explicitly");
        }
        assert_eq!(
            builder
                .finish(header(&core))
                .expect("all rows are complete"),
            *table(&core)
        );
    }

    #[test]
    fn authored_binding_unfinished_auxiliary_is_not_explicit_absence() {
        let core = fixture();
        let mut builder = AuthoredDeclarationBindingsBuilder::try_new(header(&core))
            .expect("fixture allocation succeeds");
        builder
            .bind_category(0, CategoryId(0))
            .expect("category assignment succeeds");
        for index in 0..3 {
            builder
                .bind_token_direct(index, TokenId(0))
                .expect("direct assignment succeeds");
        }
        assert_eq!(
            builder.finish(header(&core)),
            Err(AuthoredBindingError::Unfinished { field: "typed literal tokens", index: 0 })
        );
        let mut explicit = vec![None];
        bind_once(&mut explicit, 0, None::<TokenId>, "auxiliary")
            .expect("explicit absence is a write");
        assert_eq!(
            finish_slots(explicit, "auxiliary").expect("explicit absence is complete"),
            vec![None]
        );
    }

    #[test]
    fn authored_binding_validation_allows_coalescing_and_both_routes_without_decoder_claims() {
        let core = fixture();
        core.validate()
            .expect("source names may differ from qualified token names and decoder metadata");
        assert_eq!(table(&core).tokens[0].direct, table(&core).tokens[1].direct);
        let encoded = postcard::to_allocvec(&core).expect("complete Core should serialize");
        let decoded: GrammarCoreV1 =
            postcard::from_bytes(&encoded).expect("ABI4 Core should deserialize");
        assert_eq!(decoded, core);
        decoded
            .validate()
            .expect("deserialized complete table must validate");
    }

    #[test]
    fn authored_binding_validation_checks_all_counts_and_category_associations() {
        let core = fixture();
        let mut bindings = table(&core).clone();
        bindings.categories.clear();
        assert!(matches!(
            bindings.validate(store(&core), &core),
            Err(AuthoredBindingError::CountMismatch { field: "categories", .. })
        ));
        let mut bindings = table(&core).clone();
        bindings.tokens.pop();
        assert!(matches!(
            bindings.validate(store(&core), &core),
            Err(AuthoredBindingError::CountMismatch { field: "tokens", .. })
        ));
        let mut bindings = table(&core).clone();
        bindings.modes.clear();
        assert!(matches!(
            bindings.validate(store(&core), &core),
            Err(AuthoredBindingError::CountMismatch { field: "modes", .. })
        ));
        let mut bindings = table(&core).clone();
        bindings.categories[0] = CategoryId(99);
        assert!(matches!(
            bindings.validate(store(&core), &core),
            Err(AuthoredBindingError::InvalidTarget { field: "categories", .. })
        ));
        let mut renamed = core.clone();
        renamed.categories[0].name = "Different".into();
        assert!(matches!(
            table(&renamed).validate(store(&renamed), &renamed),
            Err(AuthoredBindingError::CategorySpelling { .. })
        ));
    }

    #[test]
    fn authored_binding_validation_checks_direct_auxiliary_modes_and_membership() {
        let core = fixture();
        for auxiliary in [false, true] {
            let mut bindings = table(&core).clone();
            if auxiliary {
                bindings.tokens[0].typed_literal = Some(TokenId(99));
            } else {
                bindings.tokens[0].direct = TokenId(99);
            }
            assert!(matches!(
                bindings.validate(store(&core), &core),
                Err(AuthoredBindingError::InvalidTarget { field: "tokens", .. })
            ));
            if auxiliary {
                bindings.tokens[0].typed_literal = Some(TokenId(2));
            } else {
                bindings.tokens[0].direct = TokenId(2);
            }
            assert!(matches!(
                bindings.validate(store(&core), &core),
                Err(AuthoredBindingError::TokenMode { .. })
            ));
        }
        let mut missing = core.clone();
        missing.modes[0].token_ids.retain(|id| *id != TokenId(1));
        assert!(matches!(
            table(&missing).validate(store(&missing), &missing),
            Err(AuthoredBindingError::TokenMembership { token: 1, .. })
        ));
        let mut bindings = table(&core).clone();
        bindings.modes[0] = ModeId(99);
        assert!(matches!(
            bindings.validate(store(&core), &core),
            Err(AuthoredBindingError::InvalidTarget { field: "modes", .. })
        ));
    }

    #[test]
    fn authored_binding_empty_language_still_requires_complete_publication() {
        let header = AuthoredDeclarations {
            categories: vec![],
            tokens: vec![],
            global_tokens: vec![],
            modes: vec![],
        };
        let mut core = GrammarCoreV1::new("empty");
        core.authored = Some(
            AuthoredRuleStore::new()
                .with_declarations(header.clone())
                .expect("empty header is available, not absent"),
        );
        assert!(core
            .validate()
            .expect_err("header without bindings must fail")
            .contains(&ValidationError::InvalidAuthoredBindings(
                AuthoredBindingError::PresenceMismatch
            )));
        core.authored_bindings = Some(
            AuthoredDeclarationBindingsBuilder::try_new(&header)
                .expect("empty builder reserves no rows")
                .finish(&header)
                .expect("empty rows are complete"),
        );
        core.validate()
            .expect("zero-rule declaration owner and bindings are valid");
        core.authored = None;
        assert!(core
            .validate()
            .expect_err("bindings without header must fail")
            .contains(&ValidationError::InvalidAuthoredBindings(
                AuthoredBindingError::PresenceMismatch
            )));
    }

    #[test]
    fn authored_binding_abi_and_fingerprint_commit_the_table() {
        let core = fixture();
        assert_eq!(core.abi, GRAMMAR_CORE_ABI_V4);
        let mut old = core.clone();
        old.abi = GRAMMAR_CORE_ABI_V3;
        assert!(old
            .validate()
            .expect_err("old ABI must not be silently upgraded")
            .contains(&ValidationError::UnsupportedAbi(GRAMMAR_CORE_ABI_V3)));
        let mut changed = core.clone();
        changed
            .authored_bindings
            .as_mut()
            .expect("fixture has table")
            .tokens[1]
            .direct = TokenId(1);
        changed
            .validate()
            .expect("different final association is structurally valid");
        assert_ne!(
            core.fingerprint().expect("fingerprint serializes"),
            changed
                .fingerprint()
                .expect("changed fingerprint serializes")
        );
    }

    #[test]
    fn authored_binding_native_kind_wire_preserves_all_original_variants() {
        let kinds = [
            NativeKind::Int8,
            NativeKind::Int16,
            NativeKind::Int32,
            NativeKind::Int64,
            NativeKind::Int128,
            NativeKind::Isize,
            NativeKind::UInt8,
            NativeKind::UInt16,
            NativeKind::UInt32,
            NativeKind::UInt64,
            NativeKind::UInt128,
            NativeKind::Usize,
            NativeKind::Float32,
            NativeKind::Float64,
            NativeKind::Bool,
            NativeKind::Str,
            NativeKind::CanonicalBigInt,
            NativeKind::CanonicalBigRat,
            NativeKind::CanonicalFixedPoint,
            NativeKind::Other,
        ];
        for kind in kinds {
            let bytes = postcard::to_allocvec(&kind).expect("original native variant serializes");
            assert_eq!(
                postcard::from_bytes::<NativeKind>(&bytes)
                    .expect("original native variant deserializes"),
                kind
            );
        }
    }
}
