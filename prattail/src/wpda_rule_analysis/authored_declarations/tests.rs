//! Validated source-observation fixtures, not frontend duplicate-acceptance claims.
use super::{AuthoredDeclarationReader, AuthoredDeclarationReaderError};
use crate::wpda_rule_analysis::native_first::{
    EmissionContext, LiteralFamily, NativeFirstConstructors, NativePatternSite,
};
use mettail_grammar_core::*;

struct Fixture {
    core: GrammarCoreV1,
    store: AuthoredRuleStore,
    header: AuthoredDeclarations,
    bindings: AuthoredDeclarationBindings,
}

impl Fixture {
    fn new() -> Self {
        Self {
            core: GrammarCoreV1::new("declaration-reader"),
            store: AuthoredRuleStore::new(),
            header: AuthoredDeclarations {
                categories: vec![],
                tokens: vec![],
                global_tokens: vec![],
                modes: vec![],
            },
            bindings: AuthoredDeclarationBindings::default(),
        }
    }

    fn name(&mut self, spelling: &str, equality_class: u32) -> AuthoredNameId {
        AuthoredNameId(
            self.store
                .try_push(AuthoredNode::Name(AuthoredName {
                    spelling: spelling.into(),
                    equality_class,
                }))
                .expect("fixture name is a valid shallow append"),
        )
    }

    fn category(&mut self, spelling: &str, native: Option<NativeKind>) -> AuthoredNameId {
        let class = u32::try_from(self.store.len()).expect("small fixture arena");
        let name = self.name(spelling, class);
        // Duplicate retained rows associate with one unique Core category.
        let target = match self
            .core
            .categories
            .iter()
            .position(|row| row.name == spelling)
        {
            Some(index) => CategoryId(u32::try_from(index).expect("small category index")),
            None => {
                let id = CategoryId(
                    u32::try_from(self.core.categories.len()).expect("small category roster"),
                );
                self.core.categories.push(Category {
                    id,
                    name: spelling.into(),
                    carrier: Carrier::Dynamic,
                    primary: id.0 == 0,
                    admits_variables: true,
                });
                id
            },
        };
        self.header.categories.push(AuthoredCategoryDeclaration {
            name,
            native,
            collection: None,
            byte_observation: SourceObservation::Unavailable,
            literal_observation: SourceObservation::Unavailable,
            element_observation: SourceObservation::Unavailable,
        });
        self.bindings.categories.push(target);
        name
    }

    fn rule(&mut self, category: AuthoredNameId) -> AuthoredRuleId {
        let label = self.name("Rule", 900);
        AuthoredRuleId(
            self.store
                .try_push(AuthoredNode::Rule(AuthoredRule {
                    label,
                    category,
                    term_context: None,
                    syntax_pattern: None,
                    items: vec![],
                }))
                .expect("fixture rule references prior names"),
        )
    }

    fn mode(&mut self, name: AuthoredNameId) -> usize {
        let index = self.header.modes.len();
        let id = ModeId(u32::try_from(self.core.modes.len()).expect("small mode roster"));
        self.core.modes.push(LexerMode {
            id,
            name: format!("execution-mode-{}", id.0),
            token_ids: vec![],
            raw: false,
        });
        self.header
            .modes
            .push(AuthoredModeDeclaration { name, tokens: vec![] });
        self.bindings.modes.push(id);
        index
    }

    fn token(
        &mut self,
        spelling: &str,
        category: Option<AuthoredNameId>,
        from_literals: bool,
        has_evaluation: bool,
        push: Option<AuthoredNameId>,
        mode: Option<usize>,
    ) -> u32 {
        let index = u32::try_from(self.header.tokens.len()).expect("small source token roster");
        let name = self.name(spelling, 1000 + index);
        let target =
            TokenId(u32::try_from(self.core.tokens.len()).expect("small execution token roster"));
        let mode_id = mode.map_or(ModeId(0), |index| self.bindings.modes[index]);
        self.core.tokens.push(TokenDefinition {
            id: target,
            name: format!("qualified/execution/{}", target.0),
            pattern: TokenPattern::Literal(format!("token-{}", target.0)),
            category: None,
            evaluation: None,
            priority: 0,
            mode: mode_id,
            channel: "main".into(),
            transition: ModeTransition::default(),
            decoder: TokenDecoder::Unit,
            reservation: Reservation::Contextual,
        });
        self.core.modes[mode_id.0 as usize].token_ids.push(target);
        self.header.tokens.push(AuthoredTokenDeclaration {
            name,
            category,
            from_literals,
            has_evaluation,
            push,
        });
        match mode {
            None => self.header.global_tokens.push(index),
            Some(mode) => self.header.modes[mode].tokens.push(index),
        }
        self.bindings
            .tokens
            .push(AuthoredTokenBinding { direct: target, typed_literal: None });
        index
    }

    fn finish(mut self) -> GrammarCoreV1 {
        self.core.authored = Some(
            self.store
                .with_declarations(self.header)
                .expect("fixture header has valid edges and canonical source roster"),
        );
        self.core.authored_bindings = Some(self.bindings);
        self.core
            .validate()
            .expect("positive reader fixtures fully validate");
        self.core
    }
}

#[test]
fn authored_declarations_census_preserves_five_passes_and_supplied_rule_order() {
    let mut f = Fixture::new();
    f.category("Rest", None);
    f.category("Native", Some(NativeKind::Other));
    f.category("Collection", None);
    f.header.categories[2].collection = Some(AuthoredCollectionDeclaration {
        kind: CollectionKind::List,
        open: None,
        close: None,
        separator: None,
        key_value_separator: None,
    });
    let literal = f.category("LiteralWithoutEvaluation", None);
    let modal = f.category("ModalOnly", None);
    let a = f.category("A", None);
    let b = f.category("B", None);
    let a_rule = f.rule(a);
    let b_rule = f.rule(b);
    f.token("Literal", Some(literal), true, false, None, None);
    let mode_name = f.name("Guest", 500);
    let mode = f.mode(mode_name);
    f.token("ModalLiteral", Some(modal), true, true, None, Some(mode));
    let core = f.finish();
    let mut reader = AuthoredDeclarationReader::new(&core).expect("valid census fixture");
    assert_eq!(
        reader
            .collect_category_names(&[b_rule, a_rule, b_rule])
            .expect("supplied rules have valid tags"),
        [
            "B",
            "A",
            "LiteralWithoutEvaluation",
            "Collection",
            "Native",
            "Rest",
            "ModalOnly"
        ]
    );
    assert_eq!(reader.declared_literal("LiteralWithoutEvaluation"), None);
    assert_eq!(reader.declared_literal("ModalOnly"), None);
}

#[test]
fn authored_declarations_literal_selection_returns_first_eligible_source_row() {
    let mut f = Fixture::new();
    let category = f.category("Scalar", Some(NativeKind::Other));
    let modal = f.category("Modal", Some(NativeKind::Other));
    f.token("NotLiteral", Some(category), false, true, None, None);
    f.token("NoEvaluation", Some(category), true, false, None, None);
    let expected = f.token("RawLiteral", Some(category), true, true, None, None);
    f.token("LaterLiteral", Some(category), true, true, None, None);
    // Final IDs are producer associations, not source-row positions.
    f.bindings.tokens[0].direct = TokenId(2);
    f.bindings.tokens[2].direct = TokenId(0);
    f.bindings.tokens[2].typed_literal = Some(TokenId(3));
    let mode_name = f.name("Guest", 500);
    let mode = f.mode(mode_name);
    f.token("ModalLiteral", Some(modal), true, true, None, Some(mode));
    let core = f.finish();
    let reader = AuthoredDeclarationReader::new(&core).expect("valid literal fixture");
    let selected = reader
        .declared_literal("Scalar")
        .expect("eligible source row exists");
    assert_eq!(*selected, expected);
    assert_eq!(
        reader.token_binding(expected as usize),
        Some(&AuthoredTokenBinding {
            direct: TokenId(0),
            typed_literal: Some(TokenId(3)),
        })
    );
    assert!(std::ptr::eq(selected, &reader.header().global_tokens[2]));
    assert_eq!(reader.declared_literal("Modal"), None);
    assert_eq!(reader.literal_family("Scalar"), Some(LiteralFamily::Custom));
    assert_eq!(reader.literal_family("Modal"), None);
    assert_eq!(core.tokens[expected as usize].category, None);
    assert_eq!(core.tokens[expected as usize].name, "qualified/execution/2");
}

#[test]
fn authored_declarations_first_category_none_wins_over_duplicate_native() {
    let mut f = Fixture::new();
    f.category("Duplicate", None);
    f.category("Duplicate", Some(NativeKind::Int8));
    f.category("Other", Some(NativeKind::Other));
    f.category("Integer", Some(NativeKind::Int64));
    let core = f.finish();
    let reader = AuthoredDeclarationReader::new(&core)
        .expect("duplicate source rows share one Core category");
    assert_eq!(reader.category_binding(0), reader.category_binding(1));
    assert_eq!(core.categories.len(), 3);
    assert_eq!(reader.literal_family("Duplicate"), None);
    assert_eq!(reader.literal_family("Other"), None);
    assert_eq!(reader.literal_family("Integer"), Some(LiteralFamily::Integer));
    assert_eq!(reader.literal_family("Missing"), None);
}

#[derive(Default)]
struct Constructors {
    trace: Vec<String>,
}
impl NativeFirstConstructors for Constructors {
    type Pattern = String;
    fn pattern(&mut self, site: NativePatternSite) -> String {
        let value = format!("{site:?}");
        self.trace.push(value.clone());
        value
    }
    fn category_guard(&mut self, category: &str) -> String {
        let value = format!("guard:{category}");
        self.trace.push(value.clone());
        value
    }
}

#[test]
fn authored_declarations_native_rows_keep_original_constructor_schedule() {
    let core = Fixture::new().finish();
    let reader = AuthoredDeclarationReader::new(&core).expect("empty retained owner is valid");
    let mut constructors = Constructors::default();
    let home = reader.native_rows(
        "N",
        LiteralFamily::Integer,
        Some(&NativeKind::CanonicalBigInt),
        EmissionContext::HomeCategory,
        &mut constructors,
    );
    assert_eq!(
        constructors.trace,
        [
            "IntegerTyped",
            "guard:N",
            "CustomTyped",
            "guard:N",
            "IntegerBare",
            "IntegerBare"
        ]
    );
    assert_eq!(
        home,
        vec![
            ("IntegerTyped".into(), Some("guard:N".into())),
            ("CustomTyped".into(), Some("guard:N".into())),
            ("IntegerBare".into(), None)
        ]
    );
    constructors.trace.clear();
    let first = reader.native_rows(
        "N",
        LiteralFamily::Integer,
        Some(&NativeKind::CanonicalBigInt),
        EmissionContext::FirstSet,
        &mut constructors,
    );
    assert_eq!(first, home[..2]);
    assert_eq!(constructors.trace, ["IntegerTyped", "guard:N", "CustomTyped", "guard:N"]);
}

#[test]
fn authored_declarations_guest_first_opener_without_push_does_not_fall_through() {
    let mut f = Fixture::new();
    let guest = f.name("Guest", 50);
    f.token("Open", None, false, false, None, None);
    f.token("Open", None, false, false, Some(guest), None);
    let mode = f.mode(guest);
    f.token("Nested", None, false, false, Some(guest), Some(mode));
    let core = f.finish();
    let reader = AuthoredDeclarationReader::new(&core)
        .expect("duplicate raw names have unique execution names");
    assert!(reader.guest_nested_open_kinds("Open").is_empty());
    assert!(reader.guest_nested_open_kinds("Missing").is_empty());
}

#[test]
fn authored_declarations_guest_uses_classes_but_raw_opener_spelling() {
    let mut f = Fixture::new();
    let intended = f.name("Guest", 50);
    let unequal_same_spelling = f.name("Guest", 51);
    let equal_distinct_occurrence = f.name("Guest", 50);
    f.token("r#Open", None, false, false, Some(intended), None);
    let wrong_mode = f.mode(unequal_same_spelling);
    f.token("WrongMode", None, false, false, Some(intended), Some(wrong_mode));
    let right_mode = f.mode(equal_distinct_occurrence);
    f.token("Kept", None, false, false, Some(equal_distinct_occurrence), Some(right_mode));
    f.token("WrongPush", None, false, false, Some(unequal_same_spelling), Some(right_mode));
    f.token("Kept", None, false, false, Some(intended), Some(right_mode));
    let core = f.finish();
    let reader = AuthoredDeclarationReader::new(&core)
        .expect("mode bindings validate independently of source equality");
    assert_eq!(reader.guest_nested_open_kinds("r#Open"), ["Kept", "Kept"]);
    assert!(reader.guest_nested_open_kinds("Open").is_empty());
}

#[test]
fn authored_declarations_bindings_and_data_role_use_final_core_ids() {
    let mut f = Fixture::new();
    f.category("Variable", None);
    f.category("Data", None);
    f.core.categories[1].admits_variables = false;
    f.token("Raw", None, false, false, None, None);
    let mode_name = f.name("Guest", 50);
    let mode = f.mode(mode_name);
    f.token("Raw", None, false, false, None, Some(mode));
    let core = f.finish();
    let reader =
        AuthoredDeclarationReader::new(&core).expect("zero-rule owner retains declarations");
    assert!(core.productions.is_empty());
    assert_eq!(reader.category_binding(1), Some(&CategoryId(1)));
    assert_eq!(
        reader.token_binding(1),
        Some(&AuthoredTokenBinding { direct: TokenId(1), typed_literal: None })
    );
    assert_eq!(reader.mode_binding(0), Some(&ModeId(1)));
    assert_eq!(reader.is_data(0), Some(false));
    assert_eq!(reader.is_data(1), Some(true));
    assert_eq!(reader.is_data(2), None);
    assert_eq!(reader.category_binding(2), None);
    assert_eq!(reader.token_binding(2), None);
    assert_eq!(reader.mode_binding(1), None);
}

#[test]
fn authored_declarations_reject_missing_owners_invalid_core_and_rule_handles() {
    let mut absent = GrammarCoreV1::new("absent");
    assert!(matches!(
        AuthoredDeclarationReader::new(&absent),
        Err(AuthoredDeclarationReaderError::MissingStore)
    ));
    absent.authored = Some(AuthoredRuleStore::new());
    assert!(matches!(
        AuthoredDeclarationReader::new(&absent),
        Err(AuthoredDeclarationReaderError::MissingDeclarations)
    ));
    let core = Fixture::new().finish();
    let mut missing_bindings = core.clone();
    missing_bindings.authored_bindings = None;
    assert!(matches!(
        AuthoredDeclarationReader::new(&missing_bindings),
        Err(AuthoredDeclarationReaderError::MissingBindings)
    ));
    let mut invalid = core;
    invalid.abi = GRAMMAR_CORE_ABI_V3;
    assert!(matches!(
        AuthoredDeclarationReader::new(&invalid),
        Err(AuthoredDeclarationReaderError::InvalidCore(_))
    ));
    let mut f = Fixture::new();
    let category = f.category("Expr", None);
    let rule = f.rule(category);
    let core = f.finish();
    let mut bad_binding = core.clone();
    bad_binding
        .authored_bindings
        .as_mut()
        .expect("fixture table exists")
        .categories[0] = CategoryId(99);
    assert!(matches!(
        AuthoredDeclarationReader::new(&bad_binding),
        Err(AuthoredDeclarationReaderError::InvalidCore(_))
    ));
    let mut reader = AuthoredDeclarationReader::new(&core).expect("valid rule owner");
    for invalid_rule in [AuthoredRuleId(category.0), AuthoredRuleId(u32::MAX)] {
        assert!(matches!(reader.collect_category_names(&[rule, invalid_rule]),
            Err(AuthoredDeclarationReaderError::InvalidRule(found)) if found == invalid_rule));
    }
    assert_eq!(
        reader
            .collect_category_names(&[rule])
            .expect("failed calls do not poison reader"),
        ["Expr"]
    );
}
