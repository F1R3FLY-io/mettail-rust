//! Explicit original-constructor observations, without a second normalizer.
use super::{AuthoredNormalizationError, AuthoredNormalizationEvent, AuthoredNormalizationSession};
use crate::wpda_rule_analysis::authored::AuthoredRuleReader;
use crate::wpda_rule_analysis::binder::optional::{BinderSyntaxObservation, BinderSyntaxReader};
use crate::wpda_rule_analysis::binder::rule::BinderRuleReader;
use mettail_grammar_core::*;

fn append(store: &mut AuthoredRuleStore, node: AuthoredNode) -> u32 {
    store
        .try_push(node)
        .expect("fixture node references only valid prior nodes")
}

fn name(store: &mut AuthoredRuleStore, spelling: &str, class: u32) -> AuthoredNameId {
    AuthoredNameId(append(
        store,
        AuthoredNode::Name(AuthoredName {
            spelling: spelling.into(),
            equality_class: class,
        }),
    ))
}

fn rule(
    store: &mut AuthoredRuleStore,
    category: AuthoredNameId,
    items: Vec<AuthoredLegacyItem>,
) -> AuthoredRuleId {
    AuthoredRuleId(append(
        store,
        AuthoredNode::Rule(AuthoredRule {
            label: category,
            category,
            term_context: None,
            syntax_pattern: None,
            items,
        }),
    ))
}

fn category(id: AuthoredNameId) -> AuthoredLegacyItem {
    AuthoredLegacyItem::NonTerminal {
        ident: id,
        kind: NonTerminalKind::Category,
    }
}

fn collection(
    id: AuthoredNameId,
    kind: CollectionKind,
    open: Option<&str>,
    close: Option<&str>,
    separator: &str,
) -> AuthoredLegacyItem {
    AuthoredLegacyItem::Collection {
        kind,
        element: id,
        separator: separator.into(),
        open: open.map(str::to_owned),
        close: close.map(str::to_owned),
    }
}

fn normalize(
    session: AuthoredNormalizationSession,
    id: AuthoredRuleId,
) -> (AuthoredNormalizationSession, AuthoredRuleId) {
    match session.normalize(id, |_| Ok::<_, ()>(())) {
        Ok(output) => output,
        Err(error) => panic!("admitted valid normalization fixture failed: {error:?}"),
    }
}

fn get_rule(store: &AuthoredRuleStore, id: AuthoredRuleId) -> &AuthoredRule {
    match store.get(id.0) {
        Some(AuthoredNode::Rule(rule)) => rule,
        other => panic!("expected retained Rule node, found {other:?}"),
    }
}

fn get_name(store: &AuthoredRuleStore, id: AuthoredNameId) -> &AuthoredName {
    match store.get(id.0) {
        Some(AuthoredNode::Name(name)) => name,
        other => panic!("expected retained Name node, found {other:?}"),
    }
}

fn get_type(store: &AuthoredRuleStore, id: AuthoredTypeId) -> &AuthoredType {
    match store.get(id.0) {
        Some(AuthoredNode::Type(ty)) => ty,
        other => panic!("expected retained Type node, found {other:?}"),
    }
}

fn params(store: &AuthoredRuleStore, id: AuthoredRuleId) -> Vec<&AuthoredParam> {
    let context = get_rule(store, id)
        .term_context
        .expect("normalized context exists");
    let Some(AuthoredNode::Params(ids)) = store.get(context.0) else {
        panic!("normalized context must reference Params");
    };
    ids.iter()
        .map(|id| match store.get(id.0) {
            Some(AuthoredNode::Param(param)) => param,
            other => panic!("expected retained Param node, found {other:?}"),
        })
        .collect()
}

fn simple_name(store: &AuthoredRuleStore, id: AuthoredRuleId, position: usize) -> AuthoredNameId {
    match params(store, id)[position] {
        AuthoredParam::Simple { name, .. } => *name,
        other => panic!("expected Simple at position {position}, found {other:?}"),
    }
}

fn assert_prefix(before: &AuthoredRuleStore, after: &AuthoredRuleStore) {
    assert!(after.len() >= before.len());
    for index in 0..before.len() {
        let index = u32::try_from(index).expect("small fixture index");
        assert_eq!(after.get(index), before.get(index), "original node {index}");
    }
    assert_eq!(after.declarations(), before.declarations());
    after
        .validate()
        .expect("materialized arena retains every typed-edge invariant");
}

fn event_text(event: AuthoredNormalizationEvent<'_>) -> String {
    match event {
        AuthoredNormalizationEvent::OriginalRule(id) => format!("rule:{}", id.0),
        AuthoredNormalizationEvent::Legacy(event) => format!("legacy:{event:?}"),
        AuthoredNormalizationEvent::NameNode(index) => format!("name-node:{index}"),
        AuthoredNormalizationEvent::NameLookup(text) => format!("lookup:{text}"),
        AuthoredNormalizationEvent::NameIndexEntry(text) => format!("index:{text}"),
        AuthoredNormalizationEvent::Append(node) => format!("append:{node:?}"),
        AuthoredNormalizationEvent::ParamSlots(count) => format!("params:{count}"),
        AuthoredNormalizationEvent::SyntaxSlots(count) => format!("syntax:{count}"),
        AuthoredNormalizationEvent::LegacyItems(count) => format!("items:{count}"),
        AuthoredNormalizationEvent::LegacyItem(item) => format!("item:{item:?}"),
    }
}

fn rich_fixture() -> (AuthoredRuleStore, AuthoredRuleId) {
    let mut store = AuthoredRuleStore::new();
    let result = name(&mut store, "Result", 1);
    let first = name(&mut store, "First", 2);
    let overwritten = name(&mut store, "Overwritten", 3);
    let domain = name(&mut store, "Domain", 4);
    let list = name(&mut store, "ListElement", 5);
    let body = name(&mut store, "Body", 6);
    let map = name(&mut store, "MapElement", 7);
    let last = name(&mut store, "Last", 8);
    let id = rule(
        &mut store,
        result,
        vec![
            category(first),
            AuthoredLegacyItem::Binder { category: overwritten },
            AuthoredLegacyItem::Binder { category: domain },
            AuthoredLegacyItem::Terminal("between".into()),
            collection(list, CollectionKind::List, Some("["), Some("]"), "|"),
            category(body),
            collection(map, CollectionKind::Map, Some("map("), Some("END"), "::"),
            category(last),
        ],
    );
    let store = store
        .with_declarations(AuthoredDeclarations {
            categories: vec![AuthoredCategoryDeclaration {
                name: result,
                native: None,
                collection: None,
                byte_observation: SourceObservation::Unavailable,
                literal_observation: SourceObservation::Unavailable,
                element_observation: SourceObservation::Unavailable,
            }],
            tokens: vec![],
            global_tokens: vec![],
            modes: vec![],
        })
        .expect("fixture source header is valid");
    (store, id)
}

#[test]
fn owned_normalization_matches_original_rich_constructor_observations() {
    let (store, original) = rich_fixture();
    let before = store.clone();
    let first_address = store.get(0).expect("fixture is nonempty") as *const AuthoredNode;
    let session = AuthoredNormalizationSession::new(store);
    assert_eq!(
        session
            .store()
            .get(0)
            .expect("consumed store retains first node") as *const AuthoredNode,
        first_address
    );
    let (session, normalized) = normalize(session, original);
    let store = session.store();
    assert_prefix(&before, store);
    assert_ne!(normalized, original);
    let old = get_rule(&before, original);
    let new = get_rule(store, normalized);
    assert_eq!((new.label, new.category, &new.items), (old.label, old.category, &old.items));
    let output = params(store, normalized);
    assert_eq!(output.len(), 5);
    let AuthoredParam::Simple { name: first, ty } = output[0] else {
        panic!("first original parameter is Simple")
    };
    assert_eq!(get_name(store, *first).spelling, "p0");
    assert!(
        matches!(get_type(store, *ty), AuthoredType::Base(id) if get_name(store, *id).spelling == "First")
    );
    let AuthoredParam::Abstraction { binder, body, ty } = output[2] else {
        panic!("pending binder produces Abstraction")
    };
    assert_eq!(get_name(store, *binder).spelling, "p1");
    assert_eq!(get_name(store, *body).spelling, "p2");
    let AuthoredType::Arrow { domain, codomain } = get_type(store, *ty) else {
        panic!("abstraction keeps Arrow")
    };
    assert!(
        matches!(get_type(store, *domain), AuthoredType::Base(id) if get_name(store, *id).spelling == "Domain")
    );
    assert!(
        matches!(get_type(store, *codomain), AuthoredType::Base(id) if get_name(store, *id).spelling == "Body")
    );
    assert_eq!(get_name(store, simple_name(store, normalized, 4)).spelling, "p3");
    for (position, expected_kind, expected_element) in
        [(1, CollectionKind::List, "ListElement"), (3, CollectionKind::Map, "MapElement")]
    {
        let AuthoredParam::Simple { name, ty } = output[position] else {
            panic!("collection constructor is Simple")
        };
        assert_eq!(get_name(store, *name).spelling, "elems");
        let AuthoredType::Collection { kind, element } = get_type(store, *ty) else {
            panic!("collection is not converted into Map")
        };
        assert_eq!(*kind, expected_kind);
        assert!(
            matches!(get_type(store, *element), AuthoredType::Base(id) if get_name(store, *id).spelling == expected_element)
        );
    }
    let reader =
        AuthoredRuleReader::new(store).expect("original shallow reader accepts materialization");
    let syntax = reader
        .syntax_pattern(normalized)
        .expect("normalized syntax exists");
    let observed: Vec<_> = (0..reader.sequence_len(syntax))
        .map(|index| {
            match reader
                .at(syntax, index)
                .expect("syntax index belongs to sequence")
            {
                BinderSyntaxObservation::Literal(text) => format!("literal:{text}"),
                BinderSyntaxObservation::Param(name) => format!("param:{name}"),
                BinderSyntaxObservation::Op(id) => match store.get(id.0) {
                    Some(AuthoredNode::Operation(AuthoredOperation::Sep {
                        collection,
                        separator,
                        source: None,
                    })) => format!("sep:{}:{separator}", get_name(store, *collection).spelling),
                    other => panic!("original Sep has no operation source: {other:?}"),
                },
                _ => panic!(
                    "legacy normalizer constructs only literal, parameter and separator syntax"
                ),
            }
        })
        .collect();
    assert_eq!(
        observed,
        [
            "param:p0",
            "literal:between",
            "literal:[",
            "sep:elems:|",
            "literal:]",
            "param:p1",
            "param:p2",
            "literal:map(",
            "sep:elems:::",
            "literal:END",
            "param:p3"
        ]
    );
}

#[test]
fn owned_normalization_one_session_reuses_source_and_generated_classes() {
    let mut store = AuthoredRuleStore::new();
    let category_id = name(&mut store, "Expr", 4);
    let p0 = name(&mut store, "p0", 100);
    let elems = name(&mut store, "elems", 900);
    let raw_p0 = name(&mut store, "r#p0", 901);
    let raw_elems = name(&mut store, "r#elems", 902);
    let items = vec![
        category(category_id),
        category(category_id),
        collection(category_id, CollectionKind::List, Some("["), Some("]"), ","),
    ];
    let first = rule(&mut store, category_id, items.clone());
    let second = rule(&mut store, category_id, items);
    let before = store.clone();
    let (session, first_output) = normalize(AuthoredNormalizationSession::new(store), first);
    let first_p1 = simple_name(session.store(), first_output, 1);
    let first_class = get_name(session.store(), first_p1).equality_class;
    assert_eq!(first_class, 903);
    let mut second_trace = Vec::new();
    let (session, second_output) = match session.normalize(second, |event| {
        second_trace.push(event_text(event));
        Ok::<_, ()>(())
    }) {
        Ok(output) => output,
        Err(error) => panic!("second original rule failed: {error:?}"),
    };
    assert_prefix(&before, session.store());
    assert!(
        !second_trace
            .iter()
            .any(|event| event.starts_with("name-node:")),
        "name profile is initialized once per session"
    );
    for output in [first_output, second_output] {
        assert_eq!(
            get_name(session.store(), simple_name(session.store(), output, 0)).equality_class,
            get_name(&before, p0).equality_class
        );
        assert_eq!(
            get_name(session.store(), simple_name(session.store(), output, 2)).equality_class,
            get_name(&before, elems).equality_class
        );
        assert_eq!(
            get_name(session.store(), simple_name(session.store(), output, 1)).equality_class,
            first_class
        );
        assert_ne!(
            get_name(session.store(), simple_name(session.store(), output, 0)).equality_class,
            get_name(&before, raw_p0).equality_class
        );
        assert_ne!(
            get_name(session.store(), simple_name(session.store(), output, 2)).equality_class,
            get_name(&before, raw_elems).equality_class
        );
    }
    let owned = session.into_store();
    assert_prefix(&before, &owned);
}

#[test]
fn owned_normalization_preserves_empty_strings_and_every_collection_kind() {
    for kind in [
        CollectionKind::List,
        CollectionKind::Bag,
        CollectionKind::Set,
        CollectionKind::Map,
        CollectionKind::PathMap,
    ] {
        let mut store = AuthoredRuleStore::new();
        let category_id = name(&mut store, "Expr", 0);
        let id = rule(
            &mut store,
            category_id,
            vec![collection(category_id, kind, Some(""), Some(""), "")],
        );
        let (session, output) = normalize(AuthoredNormalizationSession::new(store), id);
        let AuthoredParam::Simple { ty, .. } = params(session.store(), output)[0] else {
            panic!("collection output is Simple")
        };
        assert!(
            matches!(get_type(session.store(), *ty), AuthoredType::Collection { kind: actual, .. } if *actual == kind)
        );
        let reader = AuthoredRuleReader::new(session.store())
            .expect("all original collection kinds are readable");
        let syntax = reader
            .syntax_pattern(output)
            .expect("collection syntax exists");
        assert_eq!(reader.sequence_len(syntax), 3);
        assert!(matches!(reader.at(syntax, 0), Some(BinderSyntaxObservation::Literal(""))));
        assert!(matches!(reader.at(syntax, 2), Some(BinderSyntaxObservation::Literal(""))));
        let Some(BinderSyntaxObservation::Op(op)) = reader.at(syntax, 1) else {
            panic!("middle syntax is separator")
        };
        assert!(
            matches!(session.store().get(op.0), Some(AuthoredNode::Operation(AuthoredOperation::Sep { separator, source: None, .. })) if separator.is_empty())
        );
    }
}

#[test]
fn owned_normalization_profile_conflicts_are_lazy_until_successful_recipes() {
    for same_spelling in [true, false] {
        for outcome in 0..3 {
            let mut store = AuthoredRuleStore::new();
            let category_id = name(&mut store, "Expr", 1);
            name(&mut store, "Conflict", 7);
            let conflict = name(
                &mut store,
                if same_spelling {
                    "Conflict"
                } else {
                    "Different"
                },
                if same_spelling { 8 } else { 7 },
            );
            let items = if outcome == 1 {
                vec![AuthoredLegacyItem::Terminal("only".into())]
            } else {
                vec![category(category_id)]
            };
            let id = if outcome == 0 {
                let context = AuthoredParamsId(append(&mut store, AuthoredNode::Params(vec![])));
                AuthoredRuleId(append(
                    &mut store,
                    AuthoredNode::Rule(AuthoredRule {
                        label: category_id,
                        category: category_id,
                        term_context: Some(context),
                        syntax_pattern: None,
                        items,
                    }),
                ))
            } else {
                rule(&mut store, category_id, items)
            };
            let before = store.clone();
            let mut trace = Vec::new();
            let result = AuthoredNormalizationSession::new(store).normalize(id, |event| {
                trace.push(event_text(event));
                Ok::<_, ()>(())
            });
            if outcome == 2 {
                assert!(
                    matches!(result, Err(AuthoredNormalizationError::NameProfileConflict(found)) if found == conflict)
                );
            } else {
                let (session, unchanged) = match result {
                    Ok(output) => output,
                    Err(error) => panic!("semantic refusal must bypass name profile: {error:?}"),
                };
                assert_eq!(unchanged, id);
                assert_eq!(session.store(), &before);
                assert!(!trace.iter().any(|event| event.starts_with("name-node:")));
            }
        }
    }
}

#[test]
fn owned_normalization_half_delimiters_follow_presence_and_preflight_order() {
    for (open, close) in [(Some("["), None), (None, Some("]"))] {
        for presence in 0..3 {
            let mut store = AuthoredRuleStore::new();
            let category_id = name(&mut store, "Expr", 0);
            let context = AuthoredParamsId(append(&mut store, AuthoredNode::Params(vec![])));
            let syntax = AuthoredSyntaxId(append(&mut store, AuthoredNode::Syntax(vec![])));
            let id = AuthoredRuleId(append(
                &mut store,
                AuthoredNode::Rule(AuthoredRule {
                    label: category_id,
                    category: category_id,
                    term_context: (presence == 1).then_some(context),
                    syntax_pattern: (presence == 2).then_some(syntax),
                    items: vec![collection(category_id, CollectionKind::List, open, close, ",")],
                }),
            ));
            let before = store.clone();
            let result =
                AuthoredNormalizationSession::new(store).normalize(id, |_| Ok::<_, ()>(()));
            if presence == 0 {
                assert!(
                    matches!(result, Err(AuthoredNormalizationError::HalfDelimiter { rule, index: 0 }) if rule == id)
                );
            } else {
                let (session, output) = match result {
                    Ok(output) => output,
                    Err(error) => panic!("present sequence bypasses half-delimiter: {error:?}"),
                };
                assert_eq!(output, id);
                assert_eq!(session.store(), &before);
            }
        }
        for half_first in [false, true] {
            let mut store = AuthoredRuleStore::new();
            let category_id = name(&mut store, "Expr", 0);
            let half = collection(category_id, CollectionKind::List, open, close, ",");
            let noncategory = AuthoredLegacyItem::NonTerminal {
                ident: category_id,
                kind: NonTerminalKind::Integer,
            };
            let id = rule(
                &mut store,
                category_id,
                if half_first {
                    vec![half, noncategory]
                } else {
                    vec![noncategory, half]
                },
            );
            let before = store.clone();
            let result =
                AuthoredNormalizationSession::new(store).normalize(id, |_| Ok::<_, ()>(()));
            if half_first {
                assert!(matches!(
                    result,
                    Err(AuthoredNormalizationError::HalfDelimiter { index: 0, .. })
                ));
            } else {
                let (session, output) = match result {
                    Ok(output) => output,
                    Err(error) => panic!("earlier noncategory ends preflight: {error:?}"),
                };
                assert_eq!(output, id);
                assert_eq!(session.store(), &before);
            }
        }
    }
}

#[test]
fn owned_normalization_original_semantic_refusals_return_unchanged_store() {
    for variant in 0..4 {
        let mut store = AuthoredRuleStore::new();
        let category_id = name(&mut store, "Expr", 0);
        let items = match variant {
            0 => vec![],
            1 => vec![AuthoredLegacyItem::Terminal("literal".into())],
            2 => vec![category(category_id), AuthoredLegacyItem::Binder { category: category_id }],
            _ => vec![
                category(category_id),
                collection(category_id, CollectionKind::List, None, None, ","),
            ],
        };
        let id = rule(&mut store, category_id, items);
        let before = store.clone();
        let (session, output) = normalize(AuthoredNormalizationSession::new(store), id);
        assert_eq!(output, id);
        assert_eq!(session.into_store(), before);
    }
}

#[test]
fn owned_normalization_class_maximum_only_refuses_missing_generated_names() {
    for existing in [true, false] {
        let mut store = AuthoredRuleStore::new();
        let category_id = name(&mut store, "Expr", 0);
        let maximum = name(&mut store, if existing { "p0" } else { "Unused" }, u32::MAX);
        let id = rule(&mut store, category_id, vec![category(category_id)]);
        let result = AuthoredNormalizationSession::new(store).normalize(id, |_| Ok::<_, ()>(()));
        if existing {
            let (session, output) = match result {
                Ok(output) => output,
                Err(error) => panic!("existing MAX class hit must succeed: {error:?}"),
            };
            assert_eq!(
                get_name(session.store(), simple_name(session.store(), output, 0)).equality_class,
                u32::MAX
            );
            assert_eq!(simple_name(session.store(), output, 0), maximum);
        } else {
            assert!(matches!(result, Err(AuthoredNormalizationError::NameClassOverflow)));
        }
    }
}

#[test]
fn owned_normalization_denial_stops_each_admission_trace_and_returns_no_session() {
    let (store, id) = rich_fixture();
    let mut full = Vec::new();
    let successful = AuthoredNormalizationSession::new(store.clone()).normalize(id, |event| {
        full.push(event_text(event));
        Ok::<_, usize>(())
    });
    assert!(successful.is_ok());
    assert_eq!(full.iter().filter(|event| *event == "params:5").count(), 1);
    assert_eq!(full.iter().filter(|event| *event == "syntax:11").count(), 1);
    assert_eq!(full.iter().filter(|event| *event == "items:8").count(), 1);
    for denied in 0..full.len() {
        let mut seen = Vec::new();
        let result = AuthoredNormalizationSession::new(store.clone()).normalize(id, |event| {
            let index = seen.len();
            seen.push(event_text(event));
            if index == denied {
                Err(index)
            } else {
                Ok(())
            }
        });
        assert!(
            matches!(result, Err(AuthoredNormalizationError::Admission(index)) if index == denied),
            "denial at {}",
            full[denied]
        );
        assert_eq!(seen, full[..=denied], "no suffix executes after denied event");
    }
    // Retry starts from independently owned original input, not a leaked failed session.
    let (session, _) = normalize(AuthoredNormalizationSession::new(store.clone()), id);
    assert_prefix(&store, session.store());
}

#[test]
fn owned_normalization_rejects_wrong_tag_range_and_nonoriginal_rule() {
    let mut store = AuthoredRuleStore::new();
    let category_id = name(&mut store, "Expr", 0);
    let original = rule(&mut store, category_id, vec![category(category_id)]);
    for invalid in [AuthoredRuleId(category_id.0), AuthoredRuleId(u32::MAX)] {
        let result = AuthoredNormalizationSession::new(store.clone())
            .normalize(invalid, |_| Ok::<_, ()>(()));
        assert!(
            matches!(result, Err(AuthoredNormalizationError::InvalidOriginalRule(found)) if found == invalid)
        );
    }
    let (session, appended) = normalize(AuthoredNormalizationSession::new(store), original);
    assert_ne!(appended, original);
    assert!(
        matches!(session.normalize(appended, |_| Ok::<_, ()>(())), Err(AuthoredNormalizationError::InvalidOriginalRule(found)) if found == appended)
    );
}
